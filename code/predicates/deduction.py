# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/deduction.py

"""Useful proof manipulation maneuvers in predicate logic."""

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

def remove_assumption(proof: Proof, assumption: Formula,
                      print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of some `conclusion` formula, an assumption of
    which is `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.1

    my_assumptions = set()
    for ass in proof.assumptions:
        if ass != Schema(assumption):
            my_assumptions.add(ass)

    prover = Prover(my_assumptions, print_as_proof_forms)
    my_dict = dict()

    for index, line in enumerate(proof.lines):

        form = Formula("->", assumption, line.formula)

        if isinstance(line, Proof.UGLine):
            my_variable = line.formula.variable
            first = Formula("A", my_variable, Formula("->", assumption, line.formula.predicate))
            line1 = prover.add_ug(first, my_dict[line.predicate_line_number])
            second = form
            third = Formula("->", first, second)
            line2 = prover.add_instantiated_assumption(third, Prover.US,
                                                       {"Q" : assumption, "x" :  my_variable ,"R" : line.formula.predicate.substitute({my_variable : Term("_")})})
            my_dict[index] = prover.add_mp(second, line1, line2)

        elif isinstance(line, Proof.MPLine):
            my_dict[index] = prover.add_tautological_implication(form, {my_dict[line.antecedent_line_number], my_dict[line.conditional_line_number]})

        elif isinstance(line, Proof.AssumptionLine):

            if assumption == line.formula:
                my_dict[index] = prover.add_tautology(Formula("->", assumption, assumption))
                continue

            line1 = prover.add_instantiated_assumption(line.formula, line.assumption, line.instantiation_map)
            my_dict[index] = prover.add_tautological_implication(form, {line1})


        elif isinstance(line, Proof.TautologyLine):

            my_dict[index] = prover.add_tautology(form)


    return prover.qed()



def proof_by_way_of_contradiction(proof: Proof, assumption: Formula,
                                  print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of a contradiction, an assumption of which is
    `assumption`, to a proof of ``'~``\ `assumption`\ ``'`` from the same
    assumptions except `assumption`.

    Parameters:
        proof: valid proof of a contradiction (i.e., a formula whose negation is
            a tautology) to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Return:
        A valid proof of ``'~``\ `assumption`\ ``'`` from the same
        assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.2

    contradiction_proof = remove_assumption(proof, assumption)

    not_ass = Formula('~', assumption)

    prover = Prover(contradiction_proof.assumptions, print_as_proof_forms)

    line1 = prover.add_proof(contradiction_proof.conclusion, contradiction_proof)
    line2 = prover.add_tautology(Formula('~', proof.conclusion))

    prover.add_tautological_implication(not_ass, {line1, line2})

    return prover.qed()