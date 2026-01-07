#!/usr/bin/env python3
"""mm2metta.py -- Convert Metamath file to MeTTa
Copyright (C) 2002 Raph Levien raph (at) acm (dot) org
Copyright (C) David A. Wheeler and mmverify.py contributors
Copyright (C) 2025 Nil Geisweiller

This program is free software distributed under the MIT license;
see the file LICENSE for full license information.
SPDX-License-Identifier: MIT

Derived from https://github.com/david-a-wheeler/mmverify.py.

To run the program, type
  $ python3 mm2metta.py set.mm --logfile set.log
and set.log will have the verification results.  One can also use bash
redirections and type '$ python3 mmverify.py < set.mm 2> set.log' but this
would fail in case 'set.mm' contains (directly or not) a recursive inclusion
statement $[ set.mm $] .

To get help on the program usage, type
  $ python3 mm2metta.py -h

(nm 27-Jun-2005) mmverify.py requires that a $f hypothesis must not occur
after a $e hypothesis in the same scope, even though this is allowed by
the Metamath spec.  This is not a serious limitation since it can be
met by rearranging the hypothesis order.
(rl 2-Oct-2006) removed extraneous line found by Jason Orendorff
(sf 27-Jan-2013) ported to Python 3, added support for compressed proofs
and file inclusion
(bj 3-Apr-2022) streamlined code; obtained significant speedup (4x on set.mm)
by verifying compressed proofs without converting them to normal proof format;
added type hints
(am 29-May-2023) added typeguards
"""

import sys
import itertools
import pathlib
import argparse
import typing
import io

Label = str
Var = str
Const = str
Step = str
CompressedSteps = str
Stmttype = typing.Literal["$c", "$v", "$f", "$e", "$a", "$p", "$d", "$="]
StringOption = typing.Optional[str]
Symbol = typing.Union[Var, Const]
Stmt = list[Symbol]
Ehyp = Stmt
Fhyp = tuple[Const, Var]
Dv = tuple[Var, Var]
Proof = typing.Union[list[Step], tuple[list[Step], list[CompressedSteps]]]
Assertion = tuple[set[Dv], list[Fhyp], list[Ehyp], Stmt]
FullStmt = tuple[Stmttype, typing.Union[Stmt, Assertion]]
MeTTa = str

def is_hypothesis(stmt: FullStmt) -> typing.TypeGuard[tuple[Stmttype, Stmt]]:
    """The second component of a FullStmt is a Stmt when its first
    component is '$e' or '$f'."""
    return stmt[0] in ('$e', '$f')

def is_assertion(stmt: FullStmt) -> typing.TypeGuard[tuple[Stmttype, Assertion]]:
    """The second component of a FullStmt is an Assertion if its first
    component is '$a' or '$p'."""
    return stmt[0] in ('$a', '$p')

# Note: a script at github.com/metamath/set.mm removes from the following code
# the lines beginning with (spaces followed by) 'vprint(' using the command
#   $ sed -E '/^ *vprint\(/d' mmverify.py > mmverify.faster.py
# In order that mmverify.faster.py be valid, one must therefore not break
# 'vprint' commands over multiple lines, nor have indented blocs containing
# only vprint lines (this would create ill-indented files).


class MMError(Exception):
    """Class of Metamath errors."""
    pass


class MMKeyError(MMError, KeyError):
    """Class of Metamath key errors."""
    pass


def vprint(vlevel: int, *arguments: typing.Any) -> None:
    """Print log message if verbosity level is higher than the argument."""
    if verbosity >= vlevel:
        print(*arguments, file=logfile)


class Toks:
    """Class of sets of tokens from which functions read as in an input
    stream.
    """

    def __init__(self, file: io.TextIOWrapper) -> None:
        """Construct a 'Toks' from the given file: initialize a line buffer
        containing the lines of the file, and initialize a set of imported
        files to a singleton containing that file, so as to avoid multiple
        imports.
        """
        self.files_buf = [file]
        self.tokbuf: list[str] = []
        self.imported_files = set({pathlib.Path(file.name).resolve()})

    def read(self) -> StringOption:
        """Read the next token in the token buffer, or if it is empty, split
        the next line into tokens and read from it."""
        while not self.tokbuf:
            if self.files_buf:
                line = self.files_buf[-1].readline()
            else:
                # There is no file to read from: this can only happen if end
                # of file is reached while within a ${ ... $} block.
                raise MMError("Unclosed ${ ... $} block at end of file.")
            if line:  # split the line into a list of tokens
                self.tokbuf = line.split()
                self.tokbuf.reverse()
            else:  # no line: end of current file
                self.files_buf.pop().close()
                if not self.files_buf:
                    return None  # End of database
        tok = self.tokbuf.pop()
        vprint(90, "Token:", tok)
        return tok

    def readf(self) -> StringOption:
        """Read the next token once included files have been expanded.  In the
        latter case, the path/name of the expanded file is added to the set of
        imported files so as to avoid multiple imports.
        """
        tok = self.read()
        while tok == '$[':
            filename = self.read()
            if not filename:
                raise MMError(
                    "Unclosed inclusion statement at end of file.")
            endbracket = self.read()
            if endbracket != '$]':
                raise MMError(
                    ("Inclusion statement for file {} not " +
                     "closed with a '$]'.").format(filename))
            file = pathlib.Path(filename).resolve()
            if file not in self.imported_files:
                # wrap the rest of the line after the inclusion command in a
                # file object
                self.files_buf.append(
                    io.StringIO(
                        " ".join(
                            reversed(
                                self.tokbuf))))
                self.tokbuf = []
                self.files_buf.append(open(file, mode='r', encoding='ascii'))
                self.imported_files.add(file)
                vprint(5, 'Importing file:', filename)
            tok = self.read()
        vprint(80, "Token once included files expanded:", tok)
        return tok

    def readc(self) -> StringOption:
        """Read the next token once included files have been expanded and
        comments have been skipped.
        """
        tok = self.readf()
        while tok == '$(':
            # Note that we use 'read' in this while-loop, and not 'readf',
            # since inclusion statements within a comment are still comments
            # so should be skipped.
            # The following line is not necessary but makes things clearer;
            # note the similarity with the first three lines of 'readf'.
            tok = self.read()
            while tok and tok != '$)':
                if '$(' in tok or '$)' in tok:
                    raise MMError(
                        ("Encountered token '{}' while reading a comment. " +
                         "Comment contents should not contain '$(' nor " +
                         "'$)' as a substring.  In particular, comments " +
                         "should not nest.").format(tok))
                tok = self.read()
            if not tok:
                raise MMError("Unclosed comment at end of file.")
            assert tok == '$)'
            # 'readf' since an inclusion may follow a comment immediately
            tok = self.readf()
        vprint(70, "Token once comments skipped:", tok)
        return tok


class Frame:
    """Class of frames, keeping track of the environment."""

    def __init__(self) -> None:
        """Construct an empty frame."""
        self.v: set[Var] = set()
        self.d: set[Dv] = set()
        self.f: list[Fhyp] = []
        self.f_labels: dict[Var, Label] = {}
        self.e: list[Ehyp] = []
        self.e_labels: dict[tuple[Symbol, ...], Label] = {}
        # Note: both self.e and self.e_labels are needed since the keys of
        # self.e_labels form a set, but the order and repetitions of self.e
        # are needed.


class FrameStack(list[Frame]):
    """Class of frame stacks, which extends lists (considered and used as
    stacks).
    """

    def push(self) -> None:
        """Push an empty frame to the stack."""
        self.append(Frame())

    def add_e(self, stmt: Stmt, label: Label) -> None:
        """Add an essential hypothesis (token tuple) to the frame stack
        top.
        """
        frame = self[-1]
        frame.e.append(stmt)
        frame.e_labels[tuple(stmt)] = label
        # conversion to tuple since dictionary keys must be hashable

    def add_d(self, varlist: list[Var]) -> None:
        """Add a disjoint variable condition (ordered pair of variables) to
        the frame stack top.
        """
        self[-1].d.update((min(x, y), max(x, y))
                          for x, y in itertools.product(varlist, varlist)
                          if x != y)

    def lookup_v(self, tok: Var) -> bool:
        """Return whether the given token is an active variable."""
        return any(tok in fr.v for fr in self)

    def lookup_d(self, x: Var, y: Var) -> bool:
        """Return whether the given ordered pair of tokens belongs to an
        active disjoint variable statement.
        """
        return any((min(x, y), max(x, y)) in fr.d for fr in self)

    def lookup_f(self, var: Var) -> typing.Optional[Label]:
        """Return the label of the active floating hypothesis which types the
        given variable.
        """
        for frame in self:
            try:
                return frame.f_labels[var]
            except KeyError:
                pass
        return None  # Variable is not actively typed

    def lookup_e(self, stmt: Stmt) -> Label:
        """Return the label of the (earliest) active essential hypothesis with
        the given statement.
        """
        stmt_t = tuple(stmt)
        for frame in self:
            try:
                return frame.e_labels[stmt_t]
            except KeyError:
                pass
        raise MMKeyError(stmt_t)

    def find_vars(self, stmt: Stmt) -> set[Var]:
        """Return the set of variables in the given statement."""
        return {x for x in stmt if self.lookup_v(x)}

    def make_assertion(self, stmt: Stmt) -> Assertion:
        """Return a quadruple (disjoint variable conditions, floating
        hypotheses, essential hypotheses, conclusion) describing the given
        assertion.
        """
        e_hyps = [eh for fr in self for eh in fr.e]
        mand_vars = {tok for hyp in itertools.chain(e_hyps, [stmt])
                     for tok in hyp if self.lookup_v(tok)}
        dvs = {(x, y) for fr in self for (x, y)
               in fr.d if x in mand_vars and y in mand_vars}
        f_hyps = []
        for fr in self:
            for typecode, var in fr.f:
                if var in mand_vars:
                    f_hyps.append((typecode, var))
                    mand_vars.remove(var)
        assertion = dvs, f_hyps, e_hyps, stmt
        vprint(18, 'Make assertion:', assertion)
        return assertion


def apply_subst(stmt: Stmt, subst: dict[Var, Stmt]) -> Stmt:
    """Return the token list resulting from the given substitution
    (dictionary) applied to the given statement (token list).
    """
    result = []
    for tok in stmt:
        if tok in subst:
            result += subst[tok]
        else:
            result.append(tok)
    vprint(20, 'Applying subst', subst, 'to stmt', stmt, ':', result)
    return result


class MM:
    """Class of ("abstract syntax trees" describing) Metamath databases."""

    def __init__(self, begin_label: Label, stop_label: Label) -> None:
        """Construct an empty Metamath database."""
        self.constants: set[Const] = set()
        self.fs = FrameStack()
        self.labels: dict[Label, FullStmt] = {}
        self.proofs: dict[Label, Proof] = {}
        self.begin_label = begin_label
        self.stop_label = stop_label
        self.verify_proofs = not self.begin_label

    def add_c(self, tok: Const) -> None:
        """Add a constant to the database."""
        if '$' in tok:
            raise MMError("Character '$' not allowed in math symbol: {}".format(tok))
        if tok in self.constants:
            raise MMError(
                'Constant already declared: {}'.format(tok))
        if self.fs.lookup_v(tok):
            raise MMError(
                'Trying to declare as a constant an active variable: {}'.format(tok))
        self.constants.add(tok)

    def add_v(self, tok: Var) -> None:
        """Add a variable to the frame stack top (that is, the current frame)
        of the database.  Allow local variable declarations.
        """
        if '$' in tok:
            raise MMError("Character '$' not allowed in math symbol: {}".format(tok))
        if self.fs.lookup_v(tok):
            raise MMError('var already declared and active: {}'.format(tok))
        if tok in self.constants:
            raise MMError(
                'var already declared as constant: {}'.format(tok))
        self.fs[-1].v.add(tok)

    def add_f(self, typecode: Const, var: Var, label: Label) -> None:
        """Add a floating hypothesis (ordered pair (variable, typecode)) to
        the frame stack top (that is, the current frame) of the database.
        """
        if not self.fs.lookup_v(var):
            raise MMError('var in $f not declared: {}'.format(var))
        if typecode not in self.constants:
            raise MMError('typecode in $f not declared: {}'.format(typecode))
        if any(var in fr.f_labels for fr in self.fs):
            raise MMError(
                ("var in $f already typed by an active " +
                 "$f-statement: {}").format(var))
        frame = self.fs[-1]
        frame.f.append((typecode, var))
        frame.f_labels[var] = label

    def readstmt_aux(
            self,
            stmttype: Stmttype,
            toks: Toks,
            end_token: str) -> Stmt:
        """Read tokens from the input (assumed to be at the beginning of a
        statement) and return the list of tokens until the end_token
        (typically "$=" or "$.").
        """
        stmt = []
        tok = toks.readc()
        while tok and tok != end_token:
            is_active_var = self.fs.lookup_v(tok)
            if stmttype in {'$d', '$e', '$a', '$p'} and not (
                    tok in self.constants or is_active_var):
                raise MMError(
                    "Token {} is not an active symbol".format(tok))
            if stmttype in {
                '$e',
                '$a',
                    '$p'} and is_active_var and not self.fs.lookup_f(tok):
                raise MMError(("Variable {} in {}-statement is not typed " +
                               "by an active $f-statement).").format(tok, stmttype))
            stmt.append(tok)
            tok = toks.readc()
        if not tok:
            raise MMError(
                "Unclosed {}-statement at end of file.".format(stmttype))
        assert tok == end_token
        vprint(20, 'Statement:', stmt)
        return stmt

    def read_non_p_stmt(self, stmttype: Stmttype, toks: Toks) -> Stmt:
        """Read tokens from the input (assumed to be at the beginning of a
        non-$p-statement) and return the list of tokens until the next
        end-statement token '$.'.
        """
        return self.readstmt_aux(stmttype, toks, end_token="$.")

    def read_p_stmt(self, toks: Toks) -> tuple[Stmt, Stmt]:
        """Read tokens from the input (assumed to be at the beginning of a
        p-statement) and return the couple of lists of tokens (stmt, proof)
        appearing in "$p stmt $= proof $.".
        """
        stmt = self.readstmt_aux("$p", toks, end_token="$=")
        proof = self.readstmt_aux("$=", toks, end_token="$.")
        return stmt, proof

    def read(self, toks: Toks) -> None:
        """Read the given token list to update the database and verify its
        proofs.
        """
        self.fs.push()
        label = None
        tok = toks.readc()
        while tok and tok != '$}':
            if tok == '$c':
                for tok in self.read_non_p_stmt(tok, toks):
                    self.add_c(tok)
            elif tok == '$v':
                for tok in self.read_non_p_stmt(tok, toks):
                    self.add_v(tok)
            elif tok == '$f':
                stmt = self.read_non_p_stmt(tok, toks)
                if not label:
                    raise MMError(
                        '$f must have label (statement: {})'.format(stmt))
                if len(stmt) != 2:
                    raise MMError(
                        '$f must have length two but is {}'.format(stmt))
                self.add_f(stmt[0], stmt[1], label)
                self.labels[label] = ('$f', [stmt[0], stmt[1]])
                label = None
            elif tok == '$e':
                if not label:
                    raise MMError('$e must have label')
                stmt = self.read_non_p_stmt(tok, toks)
                self.fs.add_e(stmt, label)
                self.labels[label] = ('$e', stmt)
                label = None
            elif tok == '$a':
                if not label:
                    raise MMError('$a must have label')
                self.labels[label] = (
                    '$a', self.fs.make_assertion(
                        self.read_non_p_stmt(tok, toks)))
                label = None
            elif tok == '$p':
                if not label:
                    raise MMError('$p must have label')
                stmt, proof = self.read_p_stmt(toks)
                dvs, f_hyps, e_hyps, conclusion = self.fs.make_assertion(stmt)
                if self.verify_proofs:
                    vprint(2, 'Verify:', label)
                    self.verify(f_hyps, e_hyps, conclusion, proof)
                self.labels[label] = ('$p', (dvs, f_hyps, e_hyps, conclusion))
                self.proofs[label] = proof
                label = None
            elif tok == '$d':
                self.fs.add_d(self.read_non_p_stmt(tok, toks))
            elif tok == '${':
                self.read(toks)
            elif tok == '$)':
                raise MMError("Unexpected '$)' while not within a comment")
            elif tok[0] != '$':
                if tok in self.labels:
                    raise MMError("Label {} multiply defined.".format(tok))
                if not all(ch.isalnum() or ch in '-_.' for ch in tok):
                    raise MMError(("Only letters, digits, '_', '-', and '.' are allowed in labels: {}").format(tok))
                label = tok
                vprint(20, 'Label:', label)
                if label == self.stop_label:
                    # TODO: exit gracefully the nested calls to self.read()
                    sys.exit(0)
                if label == self.begin_label:
                    self.verify_proofs = True
            else:
                raise MMError("Unknown token: '{}'.".format(tok))
            tok = toks.readc()
        self.fs.pop()

    def treat_step(self,
                   step: FullStmt,
                   stack: list[Stmt]) -> None:
        """Carry out the given proof step (given the label to treat and the
        current proof stack).  This modifies the given stack in place.
        """
        vprint(10, 'Proof step:', step)
        if is_hypothesis(step):
            _steptype, stmt = step
            stack.append(stmt)
        elif is_assertion(step):
            _steptype, assertion = step
            dvs0, f_hyps0, e_hyps0, conclusion0 = assertion
            npop = len(f_hyps0) + len(e_hyps0)
            sp = len(stack) - npop
            if sp < 0:
                raise MMError(
                    ("Stack underflow: proof step {} requires too many " +
                     "({}) hypotheses.").format(
                        step,
                        npop))
            subst: dict[Var, Stmt] = {}
            for typecode, var in f_hyps0:
                entry = stack[sp]
                if entry[0] != typecode:
                    raise MMError(
                        ("Proof stack entry {} does not match floating " +
                         "hypothesis ({}, {}).").format(entry, typecode, var))
                subst[var] = entry[1:]
                sp += 1
            vprint(15, 'Substitution to apply:', subst)
            for h in e_hyps0:
                entry = stack[sp]
                subst_h = apply_subst(h, subst)
                if entry != subst_h:
                    raise MMError(("Proof stack entry {} does not match " +
                                   "essential hypothesis {}.")
                                  .format(entry, subst_h))
                sp += 1
            for x, y in dvs0:
                vprint(16, 'dist', x, y, subst[x], subst[y])
                x_vars = self.fs.find_vars(subst[x])
                y_vars = self.fs.find_vars(subst[y])
                vprint(16, 'V(x) =', x_vars)
                vprint(16, 'V(y) =', y_vars)
                for x0, y0 in itertools.product(x_vars, y_vars):
                    if x0 == y0 or not self.fs.lookup_d(x0, y0):
                        raise MMError("Disjoint variable violation: " +
                                      "{} , {}".format(x0, y0))
            del stack[len(stack) - npop:]
            stack.append(apply_subst(conclusion0, subst))
        vprint(12, 'Proof stack:', stack)

    def treat_normal_proof(self, proof: list[str]) -> list[Stmt]:
        """Return the proof stack once the given normal proof has been
        processed.
        """
        stack: list[Stmt] = []
        active_hypotheses = {label for frame in self.fs for labels in (frame.f_labels, frame.e_labels) for label in labels.values()}
        for label in proof:
            stmt_info = self.labels.get(label)
            if stmt_info:
                label_type = stmt_info[0]
                if label_type in {'$e', '$f'}:
                    if label in active_hypotheses:
                        self.treat_step(stmt_info, stack)
                    else:
                        raise MMError(f"The label {label} is the label of a nonactive hypothesis.")
                else:
                    self.treat_step(stmt_info, stack)
            else:
                raise MMError(f"No statement information found for label {label}")
        return stack

    def treat_compressed_proof(
            self,
            f_hyps: list[Fhyp],
            e_hyps: list[Ehyp],
            proof: list[str]) -> list[Stmt]:
        """Return the proof stack once the given compressed proof for an
        assertion with the given $f and $e-hypotheses has been processed.
        """
        # Preprocessing and building the lists of proof_ints and labels
        flabels = [self.fs.lookup_f(v) for _, v in f_hyps]
        elabels = [self.fs.lookup_e(s) for s in e_hyps]
        plabels = flabels + elabels  # labels of implicit hypotheses
        idx_bloc = proof.index(')')  # index of end of label bloc
        plabels += proof[1:idx_bloc]  # labels which will be referenced later
        compressed_proof = ''.join(proof[idx_bloc + 1:])
        vprint(5, 'Referenced labels:', plabels)
        label_end = len(plabels)
        vprint(5, 'Number of referenced labels:', label_end)
        vprint(5, 'Compressed proof steps:', compressed_proof)
        vprint(5, 'Number of steps:', len(compressed_proof))
        proof_ints = []  # integers referencing the labels in 'labels'
        cur_int = 0  # counter for radix conversion
        for ch in compressed_proof:
            if ch == 'Z':
                proof_ints.append(-1)
            elif 'A' <= ch <= 'T':
                proof_ints.append(20 * cur_int + ord(ch) - 65)  # ord('A') = 65
                cur_int = 0
            else:  # 'U' <= ch <= 'Y'
                cur_int = 5 * cur_int + ord(ch) - 84  # ord('U') = 85
        vprint(5, 'Integer-coded steps:', proof_ints)
        # Processing of the proof
        stack: list[Stmt] = []  # proof stack
        # statements saved for later reuse (marked with a 'Z')
        saved_stmts = []
        # can be recovered as len(saved_stmts) but less efficient
        n_saved_stmts = 0
        for proof_int in proof_ints:
            if proof_int == -1:  # save the current step for later reuse
                stmt = stack[-1]
                vprint(15, 'Saving step', stmt)
                saved_stmts.append(stmt)
                n_saved_stmts += 1
            elif proof_int < label_end:
                # proof_int denotes an implicit hypothesis or a label in the
                # label bloc
                self.treat_step(self.labels[plabels[proof_int] or ''], stack)
            elif proof_int >= label_end + n_saved_stmts:
                raise MMError(
                    ("Not enough saved proof steps ({} saved but calling " +
                    "the {}th).").format(
                        n_saved_stmts,
                        proof_int))
            else:  # label_end <= proof_int < label_end + n_saved_stmts
                # proof_int denotes an earlier proof step marked with a 'Z'
                # A proof step that has already been proved can be treated as
                # a dv-free and hypothesis-free axiom.
                stmt = saved_stmts[proof_int - label_end]
                vprint(15, 'Reusing step', stmt)
                self.treat_step(
                    ('$a',
                     (set(), [], [], stmt)),
                    stack)
        return stack

    def verify(
            self,
            f_hyps: list[Fhyp],
            e_hyps: list[Ehyp],
            conclusion: Stmt,
            proof: list[str]) -> None:
        """Verify that the given proof (in normal or compressed format) is a
        correct proof of the given assertion.
        """
        # It would not be useful to also pass the list of dv conditions of the
        # assertion as an argument since other dv conditions corresponding to
        # dummy variables should be 'lookup_d'ed anyway.
        if proof[0] == '(':  # compressed format
            stack = self.treat_compressed_proof(f_hyps, e_hyps, proof)
        else:  # normal format
            stack = self.treat_normal_proof(proof)
        vprint(10, 'Stack at end of proof:', stack)
        if not stack:
            raise MMError(
                "Empty stack at end of proof.")
        if len(stack) > 1:
            raise MMError(
                "Stack has more than one entry at end of proof (top " +
                "entry: {} ; proved assertion: {}).".format(
                    stack[0],
                    conclusion))
        if stack[0] != conclusion:
            raise MMError(("Stack entry {} does not match proved " +
                          " assertion {}.").format(stack[0], conclusion))
        vprint(3, 'Correct proof!')

    def dump(self) -> None:
        """Print the labels of the database."""
        print(self.labels)


class ToMeTTa:
    """Class containing methods to convert MetaMath to MeTTa."""

    def __init__(self, mm: MM) -> None:
        # Store reference of MM object
        self.mm = mm

        # Mapping between metamath tokens and MeTTa
        self.token_to_metta: dict[str, str] = {}

        # Variables
        self.token_to_metta['ph'] = '$𝜑'    # phi (U+1D711, \mitphi)
        self.token_to_metta['ps'] = '$𝜓'    # psi (U+1D713, \mitpsi)
        self.token_to_metta['ch'] = '$𝜒'    # chi (U+1D712, \mitchi)
        self.token_to_metta['th'] = '$𝜃'    # theta (U+1D703, \mittheta)
        self.token_to_metta['ta'] = '$𝜏'    # tau (U+1D70F, \mittau)
        self.token_to_metta['et'] = '$𝜂'    # eta (U+1D702, \miteta)
        self.token_to_metta['ze'] = '$𝜁'    # zeta (U+1D701, \mitzeta)
        self.token_to_metta['si'] = '$𝜎'    # sigma (U+1D70E, \mitsigma)
        self.token_to_metta['rh'] = '$𝜌'    # rho (U+1D70C, \mitrho)
        self.token_to_metta['mu'] = '$𝜇'    # mu (U+1D707, \mitmu)
        self.token_to_metta['la'] = '$𝜆'    # lambda (U+1D706, \mitlambda)
        self.token_to_metta['ka'] = '$𝜅'    # kappa (U+1D705, \mitkappa)

        # Logical connectors
        self.token_to_metta['/\\'] = '∧'    # and (U+2227, \wedge)
        self.token_to_metta['-/\\'] = '⊼'   # nand (U+22BC, \barwedge)
        self.token_to_metta['\\/'] = '∨'    # or (U+2228, \vee)
        self.token_to_metta['-\\/'] = '⊽'   # nor (U+22BD, \barvee)
        self.token_to_metta['\\/_'] = '⊻'   # xor (U+22BB, \veebar)
        self.token_to_metta['->'] = '→'     # implies (U+2192, \rightarrow)
        self.token_to_metta['-.'] = '¬'     # not (U+00AC, \neg)
        self.token_to_metta['<->'] = '↔'    # iff (U+2194, \leftrightarrow)
        self.token_to_metta['if-'] = '?:'   # if-then-else

    def tokens_to_ast(self, tokens: list[str]) -> list[any]:
        """Convert a list of tokens with parentheses to a syntax tree.

        Strip parentheses and use nested lists instead.  For instance

        tokens_to_ast(['(', 'ph', '->', '(', 'ps', '<->', 'ch', ')', ')'])

        outputs

        [['ph', '->', ['ps', '<->', 'ch']]]

        Additionally treat negation '-.' as if it were surrounded by
        parentheses.  For instance

        tokens_to_ast(['(', 'ph', '->', '-.', 'ps', ')'])

        outputs

        [['ph', '->', ['-.', 'ps']]]

        It also supports nested negations.  For instance

        tokens_to_ast(['(', 'ph', '->', '-.', '-.', 'ps', ')'])

        outputs

        [['ph', '->', ['-.', ['-.', 'ps']]]]

        Or for instance

        tokens_to_ast(['-.', '-.', '(', 'ph', '->', 'ps', ')'])

        outputs

        [['-.', ['-.', ['ph', '->', 'ps']]]]

        """

        # Code produced by Duck.ai then improved by myself to support negation
        #
        # Explanation
        #
        # - The function convert_to_nested_list takes a list of tokens
        #   as input and initializes an empty stack and result list.
        #
        # - It then iterates over each token in the input list.
        #
        # - When it encounters an open parenthesis (, it pushes the
        #   current result list onto the stack and starts a new
        #   sublist.
        #
        # - When it encounters a close parenthesis ), it pops the last
        #   sublist from the stack, appends the current sublist to it,
        #   and updates the result.
        #
        # - For any other token, it simply appends it to the current
        #   sublist.
        #
        # - Finally, it checks if there are any remaining open
        #   parentheses (i.e., a non-empty stack) and raises a
        #   ValueError if there are.
        #
        # * The function returns the resulting nested list.
        stack = []
        result = [], False      # The flag indicates a negation

        for token in tokens:
            if token == '(':
                # Start a new sublist when encountering an open parenthesis
                stack.append(result)
                result = [], False
            elif token == ')':
                # End the current sublist when encountering a close parenthesis
                if not stack:
                    raise ValueError("Mismatched parentheses")
                top_result, top_flag = stack.pop()
                top_result.append(result[0])
                result = top_result, top_flag
                while result[1]:   # Take care of negation
                    top_result, top_flag = stack.pop()
                    top_result.append(result[0])
                    result = top_result, top_flag
            elif token == '-.' or token == 'if-':
                # Start a new sublist with negation when encountering a negation
                stack.append(result)
                result = [token], True
            else:
                # Append the token to the current sublist
                result[0].append(token)
                while result[1]:   # Take care of negation
                    top_result, top_flag = stack.pop()
                    top_result.append(result[0])
                    result = top_result, top_flag

        if stack:
            raise ValueError("Mismatched parentheses")

        return result[0]

    def ast_to_metta(self, ast: list[any]) -> MeTTa:
        """Convert a metamath proposition as nested list into a MeTTa S-expression.

        For instance

        ast_to_metta(['ph', '->', ['ps', '<->', 'ch']])

        outputs

        "(→ $𝜑 ($𝜓 ↔ $𝜒))"
        """
        # Token
        if isinstance(ast, str):
            return self.token_to_metta[ast]

        # Tree
        arity = len(ast)
        if arity == 0:
            return ""
        if arity == 1:
            child = ast[0]
            return "({})".format(self.ast_to_metta(child))
        if arity == 2:
            # Assumed format: [OP ARG]
            op = ast[0]
            arg = ast[1]
            if op == '-.':
                return "({} {})".format(self.ast_to_metta(op),
                                        self.ast_to_metta(arg))
            # If it is not '-.' then it should be 'if-'
            if op == 'if-':
                assert len(arg) == 5
                cond = arg[0]
                brn1 = arg[2]
                brn2 = arg[4]
                return "({} {} {} {})".format(self.ast_to_metta(op),
                                              self.ast_to_metta(cond),
                                              self.ast_to_metta(brn1),
                                              self.ast_to_metta(brn2))
            raise ValueError(f"Operator {op} not supported")
        if arity == 3:
            # Assumed format: [ARG1 OP ARG2]
            arg1 = ast[0]
            op = ast[1]    # Assumed to be an infix connector
            arg2 = ast[2]
            return "({} {} {})".format(self.ast_to_metta(op),
                                       self.ast_to_metta(arg1),
                                       self.ast_to_metta(arg2))
        if arity == 5:
            # Assumed format: [ARG1 OP ARG2 OP ARG3]
            arg1 = ast[0]
            op1 = ast[1]
            arg2 = ast[2]
            op2 = ast[3]
            arg3 = ast[4]
            assert op1 == op2
            return "({} {} {} {})".format(self.ast_to_metta(op1),
                                          self.ast_to_metta(arg1),
                                          self.ast_to_metta(arg2),
                                          self.ast_to_metta(arg3))
        raise ValueError(f"Arity {arity} not supported")

    def is_entailment(self, flstmt: FullStmt) -> bool:
        """Return True iff the given full statement is about entailement

        For instance

        is_entailment(('$p', (set(), [('wff', 'ph')], [['|-', 'ph']], ['|-', 'ph'])))

        returns True, while

        is_entailment(('$a', (set(), [('wff', 'ph')], [], ['wff', '-.', 'ph'])))

        return False.

        """
        stmt = self.get_statement(flstmt)
        if len(stmt) == 0:
            return False
        return stmt[0] == '|-'

    def is_axiom(self, flstmt: FullStmt) -> bool:
        """Return True iff the full statement is an axiom.

        For instance

        is_axiom(('$a', (set(), [('wff', 'ph'), ('wff', 'ps')], [['|-', 'ph'], ['|-', '(', 'ph', '->', 'ps', ')']], ['|-', 'ps'])))

        returns True.

        """
        return flstmt[0] == '$a'

    def get_statement(self, flstmt: FullStmt) -> Stmt:
        """Take a full statement and access its statement.

        For instance

        get_statement(('$a', (set(), [('wff', 'ph')], [], ['wff', '-.', 'ph'])))

        outputs

        ['wff', '-.', 'ph']

        """
        if is_hypothesis(flstmt):
            return flstmt[1]
        return flstmt[1][3]

    def stmt_to_metta(self, tokens: Stmt) -> MeTTa:
        """Convert a statement as list of tokens to MeTTa S-expression.

        For instance

        stmt_to_metta(['|-', '(', 'ph', '->', 'ps', ')'])

        outputs

        "(→ $𝜑 $𝜓)"

        """

        # Convert token list to AST
        ast = self.tokens_to_ast(tokens)

        # Convert AST to MeTTa, possibly dropping '|-'
        return self.ast_to_metta(ast[1] if ast[0] == '|-' else ast)

    def assertion_to_metta(self, asrt: Assertion) -> MeTTa:
        """Convert Assertion to MeTTa.

        For instance

        assertion_to_metta((set(),
                            [('wff', 'ph'), ('wff', 'ps')],
                            [['|-', 'ph'], ['|-', '(', 'ph', '->', 'ps', ')']],
                            ['|-', 'ps']))

        outputs

        (-> $𝜑 (→ $𝜑 $𝜓) $𝜓)

        For now disjoint variables and floating hypotheses are
        ignored.

        """
        hypotheses = asrt[2]
        conclusion = asrt[3]
        hmtas = [self.stmt_to_metta(h) for h in hypotheses]
        cmta = self.stmt_to_metta(conclusion)

        if len(hmtas) == 0:
            return cmta
        return "(-> {} {})".format(" ".join(hmtas), cmta)

    def fullstmt_to_metta(self, flstmt: FullStmt) -> MeTTa:
        """Convert full statement to MeTTa.

        For instance

        fullstmt_to_metta(('$a',
                           (set(),
                            [('wff', 'ph'), ('wff', 'ps')],
                            [['|-', 'ph'], ['|-', '(', 'ph', '->', 'ps', ')']],
                            ['|-', 'ps'])))

        outputs

        (-> $𝜑 (→ $𝜑 $𝜓) $𝜓)

        """
        if is_assertion(flstmt):
            return self.assertion_to_metta(flstmt[1])
        raise ValueError("Not supported")

    def axiom_to_metta(self, label: Label, flstmt: FullStmt) -> MeTTa:
        """Convert axiom definition to MeTTa.

        For instance

        axiom_to_metta("ax-mp", (set(),
                                 [('wff', 'ph'), ('wff', 'ps')],
                                 [['|-', 'ph'], ['|-', '(', 'ph', '->', 'ps', ')']],
                                 ['|-', 'ps']))

        outputs

        (: ax-mp (-> $𝜑 (→ $𝜑 $𝜓) $𝜓))

        """
        return "(: {} {})".format(label, self.fullstmt_to_metta(flstmt))

    def get_arity(self, label: Label) -> int:
        """Get the arity of whatever is associated to the given label.

        For instance

        get_arity("ax-mp") = 2

        because ax-mp is an axiom with two essential hypotheses.

        """
        flstmt = self.mm.labels[label]
        if is_hypothesis(flstmt):
            return 0
        if is_assertion(flstmt):
            return len(flstmt[1][2])

    def is_about_wff(self, label: Label) -> bool:
        """Return True iff the label is about a wff assertion"""
        flstmt = self.mm.labels[label]
        return self.get_statement(flstmt)[0] == 'wff'

    def proof_body_to_metta(self, proof: Proof) -> MeTTa:
        """Convert proof body (assuming essential hypotheses) to MeTTa.

        The proof is assumed to have been stripped of floating
        hypotheses as well axioms about wff.

        For instance

        proof_body_to_metta(['xor12d.1', 'xor12d.2', 'bibi12d', 'notbid', 'df-xor', 'df-xor', '3bitr4g']

        outputs

        (3bitr4g df-xor df-xor (notbid (bibi12d xor12d.2 xor12d.1)))

        """
        if len(proof) == 0:
            return ""
        proof.reverse()
        return self.subproof_to_metta(proof, 0)[0]

    def subproof_to_metta(self, proof: Proof, idx: int) -> tuple[MeTTa, int]:
        """Like proof_body_to_metta but working on reversed proof with index.

        Convert non-empty subproof in reverse order starting from
        index idx into MeTTa, returning the updated index after
        reading the tokens of the subproof.

        """
        head = proof[idx]
        arity = self.get_arity(head)
        idx += 1

        # Base case
        if arity == 0:
            return head, idx

        # Recursive case
        mt_subproofs = []
        for _ in range(arity):
            mt_subproof, idx = self.subproof_to_metta(proof, idx)
            mt_subproofs.append(mt_subproof)
        mt_subproofs.reverse()
        return "({} {})".format(head, " ".join(mt_subproofs)), idx

    def strip_out_wff(self, proof: Proof) -> Proof:
        """Strip out proof steps involving wff.

        For instance

        strip_out_wff(['wph', 'wps', 'wth', 'wb', 'wn', 'wch', 'wta', 'wb', 'wn', 'wps', 'wth', 'wxo', 'wch', 'wta', 'wxo', 'wph', 'wps', 'wth', 'wb', 'wch', 'wta', 'wb', 'wph', 'wps', 'wch', 'wth', 'wta', 'xor12d.1', 'xor12d.2', 'bibi12d', 'notbid', 'wps', 'wth', 'df-xor', 'wch', 'wta', 'df-xor', '3bitr4g'])

        outputs

        ['xor12d.1', 'xor12d.2', 'bibi12d', 'notbid', 'df-xor', 'df-xor', '3bitr4g']

        """
        return [s for s in proof if not self.is_about_wff(s)]

    def proof_to_metta(self, e_labels: list[Label], proof: Proof) -> MeTTa:

        """Convert proof to MeTTa.

        For instance

        proof_to_metta(['xor12d.1', 'xor12d.2'], ['wph', 'wps', 'wth', 'wb', 'wn', 'wch', 'wta', 'wb', 'wn', 'wps', 'wth', 'wxo', 'wch', 'wta', 'wxo', 'wph', 'wps', 'wth', 'wb', 'wch', 'wta', 'wb', 'wph', 'wps', 'wch', 'wth', 'wta', 'xor12d.1', 'xor12d.2', 'bibi12d', 'notbid', 'wps', 'wth', 'df-xor', 'wch', 'wta', 'df-xor', '3bitr4g'])

        outputs

        (λ xor12d.1 xor12d.2 (3bitr4g (notbid (bibi12d xor12d.1 xor12d.2)) df-xor df-xor))

        """

        # Filter out wff proof steps
        proof_wo_wff = self.strip_out_wff(proof)

        # Build proof body
        proof_body = self.proof_body_to_metta(proof_wo_wff)

        # Return full proof
        if len(e_labels) == 0:
            return proof_body
        return "(λ {} {})".format(" ".join(e_labels), proof_body)

    def get_essential_hypothesis(self, label: Label) -> list():
        """Return essential with given label, or empty if does not exists.

        For instance

        get_essential_hypothesis('xor12d.1')

        outputs

        ['|-', '(', 'ph', '->', '(', 'ps', '<->', 'ch', ')', ')']

        """
        flstmt = self.mm.labels[label]
        if flstmt[0] == '$e':
            return flstmt[1]
        return []

    def get_essential_labels(self, proof: Proof, flstmt: FullStmt) -> list[Label]:
        """Return list of labels of essential hypotheses in proof, in order."""
        ehyps = flstmt[1][2]
        idx_to_e_label = {ehyps.index(self.get_essential_hypothesis(step)) : step
                          for step in proof
                          if self.get_essential_hypothesis(step) in ehyps}
        # In case the proof does not use all essential hypotheses
        if len(idx_to_e_label) != len(ehyps):
            ehyp = list(idx_to_e_label.values())[0]
            prefix, _ = ehyp.split('.')
            idx_to_e_label = {idx : '.'.join([prefix, str(idx + 1)])
                              for idx in range(len(ehyps))}
        return [v for k, v in sorted(idx_to_e_label.items())]

    def proven_theorem_to_metta(self, proof: Proof, flstmt: FullStmt) -> MeTTa:
        """Convert proven theorem to MeTTa.

        For instance

        proven_theorem_to_metta(['wph', 'wps', 'wth', 'wb', 'wn', 'wch', 'wta', 'wb', 'wn', 'wps', 'wth', 'wxo', 'wch', 'wta', 'wxo', 'wph', 'wps', 'wth', 'wb', 'wch', 'wta', 'wb', 'wph', 'wps', 'wch', 'wth', 'wta', 'xor12d.1', 'xor12d.2', 'bibi12d', 'notbid', 'wps', 'wth', 'df-xor', 'wch', 'wta', 'df-xor', '3bitr4g'], ('$p', (set(), [('wff', 'ph'), ('wff', 'ps'), ('wff', 'ch'), ('wff', 'th'), ('wff', 'ta')], [['|-', '(', 'ph', '->', '(', 'ps', '<->', 'ch', ')', ')'], ['|-', '(', 'ph', '->', '(', 'th', '<->', 'ta', ')', ')']], ['|-', '(', 'ph', '->', '(', '(', 'ps', '\\/_', 'th', ')', '<->', '(', 'ch', '\\/_', 'ta', ')', ')', ')'])))

        outputs

        (: (λ xor12d.1 xor12d.2 (3bitr4g (notbid (bibi12d xor12d.1 xor12d.2)) df-xor df-xor)) (-> (→ $𝜑 (↔ $𝜓 $𝜒)) (→ $𝜑 (↔ $𝜃 $𝜏)) (→ $𝜑 (↔ (⊻ $𝜓 $𝜃) (⊻ $𝜒 $𝜏)))))

        """
        # Gather labels of essential hypotheses
        e_labels = self.get_essential_labels(proof, flstmt)

        # Output proven theorem
        return "(: {} {})".format(self.proof_to_metta(e_labels, proof),
                                  self.fullstmt_to_metta(flstmt))

    def to_metta(self) -> MeTTa:
        """Convert the full Metamath corpus into MeTTa.

        Create the following type definitions

        ```
        ;; Assertion, either axiom or theorem
        (: Assertion Type)
        (: MkAxiom (-> Symbol Atom Assertion))
        (: MkTheorem (-> Symbol Atom Atom Assertion))

        ;; Indexed assertion
        (: Indexed Type)
        (: MkIndexed (-> Number Assertion Indexed))
        ```

        alongside data such as

        ```
        (MkIndexed 0 (MkTheorem idi (λ idi.1 idi.1) (-> $𝜑 $𝜑)))
        ```

        where
        - 0 is the index of the assertion (here a theorem)
        - `idi` is the label of the theorem
        - `(λ idi.1 idi.1)` is the proof of the theorem
        - `(-> $𝜑 $𝜑)` is the statement of the theorem

        or

        ```
        (MkIndexed 2 (MkAxiom ax-mp (-> $𝜑 (→ $𝜑 $𝜓) $𝜓)))
        ```

        where
        - 2 is the index of the assertion (here an axiom)
        - `ax-mp` is the label of the axiom
        - `(-> $𝜑 (→ $𝜑 $𝜓) $𝜓)` is the statement if the axiom

        Only assertions about entailement `|-` are considered,
        i.e. assertions about `wff` are ignored.

        """
        # Define indexed assertion type
        type_defs = []
        type_defs.append(";;;;;;;;;")
        type_defs.append("; Types ;")
        type_defs.append(";;;;;;;;;")
        type_defs.append("")
        type_defs.append(";; Assertion, either axiom or theorem")
        type_defs.append("(: Assertion Type)")
        type_defs.append("(: MkAxiom (-> Symbol ; Label")
        type_defs.append("               Atom   ; Axiom")
        type_defs.append("               Assertion))")
        type_defs.append("(: MkTheorem (-> Symbol ; Label")
        type_defs.append("                 Atom   ; Proof")
        type_defs.append("                 Atom   ; Theorem")
        type_defs.append("                 Assertion))")
        type_defs.append("")
        type_defs.append(";; Indexed assertion")
        type_defs.append("(: Indexed Type)")
        type_defs.append("(: MkIndexed (-> Number    ; Index")
        type_defs.append("                 Assertion ; Axiom or Theorem")
        type_defs.append("                 Indexed))")
        type_defs.append("")

        # Populate indexed assertions
        data = []
        data.append(";;;;;;;;")
        data.append("; Data ;")
        data.append(";;;;;;;;")
        data.append("")
        idx = 0
        for label, flstmt in self.mm.labels.items():
            if is_assertion(flstmt) and self.is_entailment(flstmt):
                mt_stmt = self.fullstmt_to_metta(flstmt)
                if self.is_axiom(flstmt): # Axiom
                    mt_assertion =  f"(MkAxiom {label} {mt_stmt})"
                else:                     # Theorem
                    proof = self.mm.proofs[label]
                    e_labels = self.get_essential_labels(proof, flstmt)
                    hypotheses = flstmt[1][2]
                    assert len(e_labels) == len(hypotheses)
                    mt_proof = self.proof_to_metta(e_labels, proof)
                    mt_assertion = f"(MkTheorem {label} {mt_proof} {mt_stmt})"
                data.append(f"(MkIndexed {idx} {mt_assertion})")
                idx += 1
        return "\n".join(type_defs) + "\n" + "\n".join(data) + "\n"


if __name__ == '__main__':
    """Parse the arguments and verify the given Metamath database."""
    parser = argparse.ArgumentParser(description="""Verify a Metamath database.
      The grammar of the whole file is verified.  Proofs are verified between
      the statements with labels BEGIN_LABEL (included) and STOP_LABEL (not
      included).

      One can also use bash redirections:
         '$ python3 mmverify.py < file.mm 2> file.log'
      in place of
         '$ python3 mmverify.py file.mm --logfile file.log'
      but this fails in case 'file.mm' contains (directly or not) a recursive
      inclusion statement '$[ file.mm $]'.""")
    parser.add_argument(
        'database',
        nargs='?',
        type=argparse.FileType(
            mode='r',
            encoding='ascii'),
        default=sys.stdin,
        help="""database (Metamath file) to verify, expressed using relative
          path (defaults to <stdin>)""")
    parser.add_argument(
        '-l',
        '--logfile',
        dest='logfile',
        type=argparse.FileType(
            mode='w',
            encoding='ascii'),
        default=sys.stderr,
        help="""file to output logs, expressed using relative path (defaults to
          <stderr>)""")
    parser.add_argument(
        '-v',
        '--verbosity',
        dest='verbosity',
        default=0,
        type=int,
        help='verbosity level (default=0 is mute; higher is more verbose)')
    parser.add_argument(
        '-b',
        '--begin-label',
        dest='begin_label',
        type=str,
        help="""label where to begin verifying proofs (included, if it is a
          provable statement)""")
    parser.add_argument(
        '-s',
        '--stop-label',
        dest='stop_label',
        type=str,
        help='label where to stop verifying proofs (not included)')
    args = parser.parse_args()
    verbosity = args.verbosity
    db_file = args.database
    logfile = args.logfile
    vprint(1, 'mmverify.py -- Proof verifier for the Metamath language')
    mm = MM(args.begin_label, args.stop_label)
    vprint(1, 'Reading source file "{}"...'.format(db_file.name))
    mm.read(Toks(db_file))
    vprint(1, 'No errors were found.')
    # mm.dump()

    # Convert content of mm to MeTTa and write the result to stdout
    sys.stdout.write(ToMeTTa(mm).to_metta())
