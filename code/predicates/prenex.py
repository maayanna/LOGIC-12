# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/prenex.py

"""Conversion of predicate-logic formulas into prenex normal form."""

from typing import Tuple

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

#: Additional axioms of quantification for first-order predicate logic.
ADDITIONAL_QUANTIFICATION_AXIOMS = (
    Schema(Formula.parse('((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
                         '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                         '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                         '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                         '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                         '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                         '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
           {'x', 'y', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
           {'x', 'y', 'R', 'Q'}))

def is_quantifier_free(formula: Formula) -> bool:
    """Checks if the given formula contains any quantifiers.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if the given formula contains any quantifiers, ``True``
        otherwise.
    """
    # Task 11.3.1

    if is_quantifier(formula.root):
        return False

    if is_binary(formula.root):
        return is_quantifier_free(formula.first) and is_quantifier_free(formula.second)

    if is_unary(formula.root):
        return is_quantifier_free(formula.first)

    return True



def is_in_prenex_normal_form(formula: Formula) -> bool:
    """Checks if the given formula is in prenex normal form.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula in prenex normal form, ``False``
        otherwise.
    """
    # Task 11.3.2

    if is_quantifier(formula.root):
        return is_in_prenex_normal_form(formula.predicate)

    return is_quantifier_free(formula)

def equivalence_of(formula1: Formula, formula2: Formula) -> Formula:
    """States the equivalence of the two given formulas as a formula.

    Parameters:
        formula1: first of the formulas the equivalence of which is to be
            stated.
        formula2: second of the formulas the equivalence of which is to be
            stated.

    Returns:
        The formula ``'((``\ `formula1`\ ``->``\ `formula2`\ ``)&(``\ `formula2`\ ``->``\ `formula1`\ ``))'``.
    """
    return Formula('&', Formula('->', formula1, formula2),
                   Formula('->', formula2, formula1))

def has_uniquely_named_variables(formula: Formula) -> bool:
    """Checks if the given formula has uniquely named variables.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if in the given formula some variable name has both quantified
        and free occurrences or is quantified by more than one quantifier,
        ``True`` otherwise.
    """
    forbidden_variables = set(formula.free_variables())
    def has_uniquely_named_variables_helper(formula: Formula) -> bool:
        if is_unary(formula.root):
            return has_uniquely_named_variables_helper(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_helper(formula.first) and \
                   has_uniquely_named_variables_helper(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_helper(formula.predicate)
        else:
            assert is_relation(formula.root) or is_equality(formula.root)
            return True

    return has_uniquely_named_variables_helper(formula)


def __quantifier_helper(formula, prover):

    form, proof = uniquely_rename_quantified_variables(formula.predicate)
    my_variable = next(fresh_variable_name_generator)

    new_form = Formula(formula.root, my_variable, form.substitute({formula.variable:Term(my_variable)}))

    if formula.root == "A":
        my_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[14] #axiom number 15

    else: # formula.root == "E"
        my_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[15] #axiom number 16

    step1 = prover.add_proof(proof.conclusion, proof)

    my_dict = {'R':str(formula.predicate.substitute({formula.variable:Term("_")})),  'Q':str(form.substitute({formula.variable:Term("_")})), "x":formula.variable, "y": my_variable}
    ccl = equivalence_of(formula, new_form)
    form2 = Formula("->", proof.conclusion, ccl)
    step2 = prover.add_instantiated_assumption(form2, my_axiom, my_dict)

    prover.add_mp(ccl, step1, step2)
    return new_form, prover.qed()



def uniquely_rename_quantified_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, with the exact same structure but with the additional
        property of having uniquely named variables, obtained by consistently
        replacing each variable name that is bound in the given formula with a
        new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``. The
        second element of the pair is a proof of the equivalence of the given
        formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.
    """
    # Task 11.5

    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))

    if is_quantifier_free(formula):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()

    if is_unary(formula.root):

        form, proof = uniquely_rename_quantified_variables(formula.first)
        new_form = Formula("~", form)

        ccl = equivalence_of(formula, new_form)
        step1 = prover.add_proof(proof.conclusion, proof)
        prover.add_tautological_implication(ccl, [step1])

        return new_form, prover.qed()


    if is_quantifier(formula.root):

        return __quantifier_helper(formula, prover)

    else: # is_binary

        form1, proof1 = uniquely_rename_quantified_variables(formula.first)
        form2, proof2 = uniquely_rename_quantified_variables(formula.second)

        new_form = Formula(formula.root, form1, form2)
        ccl = equivalence_of(formula, new_form)

        step1 = prover.add_proof(proof1.conclusion, proof1)
        step2 = prover.add_proof(proof2.conclusion, proof2)

        prover.add_tautological_implication(ccl, [step2, step1])
        return new_form, prover.qed()


def pull_out_quantifications_across_negation(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``,
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, whose root is a negation, i.e., which is of
            the form
            ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
            where `n`>=0, each `Qi` is a quantifier, each `xi` is a variable
            name, and `inner_formula` does not start with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the `xi` variable names and
        `inner_formula` are the same as in the given formula. The second element
        of the pair is a proof of the equivalence of the given formula and the
        returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~Ax[Ey[R(x,y)]]')
        >>> returned_formula, proof = pull_out_quantifications_across_negation(
        ...     formula)
        >>> returned_formula
        Ex[Ay[~R(x,y)]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert is_unary(formula.root)
    # Task 11.6

    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))

    # Basic Case - No quantifier to change
    if not is_quantifier(formula.first.root):
        ccl = equivalence_of(formula, formula)
        prover.add_tautology(ccl)
        return formula, prover.qed()

    # The ~ and the predicate without the quantifier to keep changing it
    form = Formula("~", formula.first.predicate)
    pred, proof = pull_out_quantifications_across_negation(form)

    # Definig the new quantifier
    if formula.first.root == "A":
        my_quantifier = "E"
    else: # "E"
        my_quantifier = "A"

    # proof for changing quantifier
    # because add_proof() is my friend
    step1 = prover.add_proof(proof.conclusion, proof)


    form2 = Formula("->", proof.conclusion, equivalence_of(Formula(my_quantifier, formula.first.variable, form),
                                                           Formula(my_quantifier, formula.first.variable, pred)))
    my_map2 = {'R': str(form.substitute({formula.first.variable: Term("_")})),
               'Q': str(pred.substitute({formula.first.variable: Term("_")})), "x": formula.first.variable, "y": formula.first.variable}

    step2 = prover.add_instantiated_assumption(form2,
                                               ADDITIONAL_QUANTIFICATION_AXIOMS[14 if my_quantifier=="A" else 15], my_map2)

    step3 = prover.add_mp(equivalence_of(Formula(my_quantifier, formula.first.variable, form),
                                         Formula(my_quantifier, formula.first.variable, pred)), step1, step2)


    my_map4 = {'R': str(formula.first.predicate.substitute({formula.first.variable: Term("_")})), "x": formula.first.variable}
    form4 = equivalence_of(formula, Formula(my_quantifier, formula.first.variable, form))
    step4 = prover.add_instantiated_assumption(form4,
                                               ADDITIONAL_QUANTIFICATION_AXIOMS[0 if my_quantifier=="E" else 1], my_map4)

    prover.add_tautological_implication(equivalence_of(formula, Formula(my_quantifier, formula.first.variable, pred)), [step3, step4])

    return Formula(my_quantifier, formula.first.variable, pred), prover.qed()



def pull_out_quantifications_from_left_across_binary_operator(formula:
                                                              Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.1


    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))

    # Basic Case - No quantifier to change n = 0 and no n = 1
    if not is_quantifier(formula.first.root):
        ccl = equivalence_of(formula, formula)
        prover.add_tautology(ccl)
        return formula, prover.qed()


    # Without the predicate
    form = Formula(formula.root, formula.first.predicate, formula.second)
    pred, proof = pull_out_quantifications_from_left_across_binary_operator(form)

    my_quantifier = formula.first.root

    # Define (or change) the quantifier and define the axioms depending on the binary operator
    if formula.root == "->":
        if my_quantifier == "A":
            my_quantifier = "E"
            axiom_scd = 10
        else:  # "E"
            my_quantifier = "A"
            axiom_scd = 11

    elif formula.root == "&":
        axiom_scd = 2 if my_quantifier == "A" else 3

    else: # "|" or
        axiom_scd = 6 if my_quantifier == "A" else 7



    # proof for changing quantifier
    # because add_proof() is my friend
    step1 = prover.add_proof(proof.conclusion, proof)

    form2 = Formula("->", proof.conclusion, equivalence_of(Formula(my_quantifier, formula.first.variable, form),
                                                           Formula(my_quantifier, formula.first.variable, pred)))
    my_map2 = {'R': str(form.substitute({formula.first.variable: Term("_")})),
               'Q': str(pred.substitute({formula.first.variable: Term("_")})), "x": formula.first.variable, "y": formula.first.variable}

    step2 = prover.add_instantiated_assumption(form2,
                                               ADDITIONAL_QUANTIFICATION_AXIOMS[14 if my_quantifier=="A" else 15], my_map2)

    step3 = prover.add_mp(equivalence_of(Formula(my_quantifier, formula.first.variable, form),
                                         Formula(my_quantifier, formula.first.variable, pred)), step1, step2)


    my_map4 = {'R': str(formula.first.predicate.substitute({formula.first.variable: Term("_")})), "x": formula.first.variable, "Q" : str(formula.second)}
    form4 = equivalence_of(formula, Formula(my_quantifier, formula.first.variable, form))
    step4 = prover.add_instantiated_assumption(form4,
                                               ADDITIONAL_QUANTIFICATION_AXIOMS[axiom_scd], my_map4)

    prover.add_tautological_implication(equivalence_of(formula, Formula(my_quantifier, formula.first.variable, pred)), [step3, step4])

    return Formula(my_quantifier, formula.first.variable, pred), prover.qed()



def pull_out_quantifications_from_right_across_binary_operator(formula:
                                                               Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_second` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `first`, and `inner_second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]|Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_from_right_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ez[(Ax[Ey[R(x,y)]]|P(1,z))]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.2


    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))

    # Basic Case - No quantifier to change n = 0 and no n = 1
    if not is_quantifier(formula.second.root):
        ccl = equivalence_of(formula, formula)
        prover.add_tautology(ccl)
        return formula, prover.qed()


    # Without the predicate
    form = Formula(formula.root, formula.first, formula.second.predicate)
    pred, proof = pull_out_quantifications_from_right_across_binary_operator(form)

    my_quantifier = formula.second.root

    # Define (or change) the quantifier and define the axioms depending on the binary operator
    if formula.root == "->":
        axiom_scd = 12 if my_quantifier == "A" else 13

    elif formula.root == "&":
        axiom_scd = 4 if my_quantifier == "A" else 5

    else: # "|" or
        axiom_scd = 8 if my_quantifier == "A" else 9



    # proof for changing quantifier
    # because add_proof() is my friend
    step1 = prover.add_proof(proof.conclusion, proof)

    form2 = Formula("->", proof.conclusion, equivalence_of(Formula(my_quantifier, formula.second.variable, form),
                                                           Formula(my_quantifier, formula.second.variable, pred)))
    my_map2 = {'R': str(form.substitute({formula.second.variable: Term("_")})),
               'Q': str(pred.substitute({formula.second.variable: Term("_")})), "x": formula.second.variable, "y": formula.second.variable}

    step2 = prover.add_instantiated_assumption(form2,
                                               ADDITIONAL_QUANTIFICATION_AXIOMS[14 if my_quantifier=="A" else 15], my_map2)

    step3 = prover.add_mp(equivalence_of(Formula(my_quantifier, formula.second.variable, form),
                                         Formula(my_quantifier, formula.second.variable, pred)), step1, step2)


    my_map4 = {'R': str(formula.second.predicate.substitute({formula.second.variable: Term("_")})), "x": formula.second.variable, "Q" : str(formula.first)}
    form4 = equivalence_of(formula, Formula(my_quantifier, formula.second.variable, form))
    step4 = prover.add_instantiated_assumption(form4,
                                               ADDITIONAL_QUANTIFICATION_AXIOMS[axiom_scd], my_map4)

    prover.add_tautological_implication(equivalence_of(formula, Formula(my_quantifier, formula.second.variable, pred)), [step3, step4])

    return Formula(my_quantifier, formula.second.variable, pred), prover.qed()


def __across_helper(formula: Formula):

    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))

    if is_quantifier(formula.root):
        form, proof = __across_helper(formula.predicate)
        step1 = prover.add_proof(proof.conclusion, proof)

        map = {"x": formula.variable, "y": formula.variable, "R": formula.predicate.substitute({formula.variable:Term("_")}), "Q": form.substitute({formula.variable:Term("_")})}
        step2 = prover.add_instantiated_assumption(ADDITIONAL_QUANTIFICATION_AXIOMS[14 if formula.root == "A" else 15].instantiate(map), ADDITIONAL_QUANTIFICATION_AXIOMS[14 if formula.root == "A" else 15], map)

        prover.add_tautological_implication(ADDITIONAL_QUANTIFICATION_AXIOMS[14 if formula.root == "A" else 15].instantiate(map).second, [step2, step1])

        return Formula(formula.root, formula.variable, form), prover.qed()


    form, proof = pull_out_quantifications_from_right_across_binary_operator(formula)
    prover.add_proof(proof.conclusion,proof)
    return form, prover.qed()



def pull_out_quantifications_across_binary_operator(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, `m`>=0, each `Qi` and `Pi`
            is a quantifier, each `xi` and `yi` is a variable name, and neither
            `inner_first` nor `inner_second` starts with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
        where each `Q'i` and `P'i` is a quantifier, and where the operator `*`,
        the `xi` and `yi` variable names, `inner_first`, and `inner_second` are
        the same as in the given formula. The second element of the pair is a
        proof of the equivalence of the given formula and the returned formula
        (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]->Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ex[Ay[Ez[(R(x,y)->P(1,z))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.8


    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))

    # if is_quantifier_free(formula):
    #     ccl = equivalence_of(formula, formula)
    #     prover.add_tautology(ccl)
    #     return formula, prover.qed()

    left_f, left_p = pull_out_quantifications_from_left_across_binary_operator(formula)

    right_f, right_p = __across_helper(left_f)

    step1 = prover.add_proof(left_p.conclusion, left_p)
    step2 = prover.add_proof(right_p.conclusion, right_p)

    prover.add_tautological_implication(equivalence_of(formula,right_f), [step2, step1])

    return right_f, prover.qed()



def to_prenex_normal_form_from_uniquely_named_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables to an equivalent
    formula in prenex normal form, and proves the equivalence of these two
    formulas.

    Parameters:
        formula: formula with uniquely named variables to convert.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(~(Ax[Ey[R(x,y)]]->Ez[P(1,z)])|S(w))')
        >>> returned_formula, proof = to_prenex_normal_form_from_uniquely_named_variables(
        ...     formula)
        >>> returned_formula
        Ax[Ey[Az[(~(R(x,y)->P(1,z))|S(w))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    # Task 11.9

    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))

    # First case
    if is_relation(formula.root) or is_equality(formula.root):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()

    elif is_unary(formula.root):
        form, proof = to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        step1 = prover.add_proof(proof.conclusion, proof)
        step2 = prover.add_tautological_implication(equivalence_of(formula, Formula("~", form)), [step1])

        neg_form, neg_proof = pull_out_quantifications_across_negation(Formula("~", form))
        step3 = prover.add_proof(neg_proof.conclusion, neg_proof)

        prover.add_tautological_implication(equivalence_of(formula, neg_form), [step2, step3])

        return neg_form, prover.qed()

    elif is_binary(formula.root):
        left_f, left_p = to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        step1 = prover.add_proof(left_p.conclusion, left_p)

        right_f, right_p = to_prenex_normal_form_from_uniquely_named_variables(formula.second)
        step2 = prover.add_proof(right_p.conclusion, right_p)

        form, proof = pull_out_quantifications_across_binary_operator(Formula(formula.root, left_f, right_f))
        step3 =prover.add_proof(proof.conclusion, proof)

        step4 = prover.add_tautological_implication(equivalence_of(Formula(formula.root, formula.first, formula.second), Formula(formula.root, left_f, right_f)), [step1, step2])

        prover.add_tautological_implication(equivalence_of(Formula(formula.root, formula.first, formula.second), form), [step4, step3])

        return form, prover.qed()


    else: # is_quantifier(formula.root)
        form, proof = to_prenex_normal_form_from_uniquely_named_variables(formula.predicate)

        step1 = prover.add_proof(proof.conclusion, proof)

        map = {"x":formula.variable, "y":formula.variable, "R":form.substitute({formula.variable: Term("_")}), "Q":formula.predicate.substitute({formula.variable:Term("_")})}
        step2 = prover.add_instantiated_assumption(ADDITIONAL_QUANTIFICATION_AXIOMS[14 if formula.root == "A" else 15].instantiate(map), ADDITIONAL_QUANTIFICATION_AXIOMS[14 if formula.root == "A" else 15], map)

        prover.add_tautological_implication(equivalence_of(formula, Formula(formula.root, formula.variable, form)), [step2, step1])

        return Formula(formula.root, formula.variable, form), prover.qed()


def to_prenex_normal_form(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula in prenex normal
    form, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.
    """
    # Task 11.10

    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))


    form, form_proof = uniquely_rename_quantified_variables(formula)
    prenex, prenex_proof = to_prenex_normal_form_from_uniquely_named_variables(form)

    step1 = prover.add_proof(form_proof.conclusion, form_proof)
    step2 = prover.add_proof(prenex_proof.conclusion, prenex_proof)

    ccl = equivalence_of(formula, prenex)
    prover.add_tautological_implication(ccl, [step1, step2])

    return prenex, prover.qed()