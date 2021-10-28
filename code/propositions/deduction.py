# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in propositional logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *

def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` into a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)
    # Task 5.3a

    myLines = list()

    for line in antecedent_proof.lines:
        myLines.append(line)

    my_map = InferenceRule.formula_specialization_map(conditional.conclusion.second, consequent)

    myLines.append(Proof.Line(conditional.specialize(my_map).conclusion, conditional, []))
    myLines.append(Proof.Line(consequent, MP, [len(antecedent_proof.lines)-1,len(antecedent_proof.lines)]))

    rules = list()
    for r in antecedent_proof.rules:
        rules.append(r)
    rules.append(MP)
    rules.append(conditional)

    my_state = InferenceRule(antecedent_proof.statement.assumptions, consequent)

    return Proof(my_state, tuple(rules), myLines)


def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulae `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``('``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
        Formula('->', antecedent2_proof.statement.conclusion, consequent))
        ).is_specialization_of(double_conditional)
    # Task 5.3b

    lines = list()

    lines.extend(antecedent1_proof.lines)
    my_map_1 = InferenceRule.formula_specialization_map(double_conditional.conclusion.first, antecedent1_proof.statement.conclusion)
    my_map_2 = InferenceRule.formula_specialization_map(double_conditional.conclusion.second.second, consequent)
    my_map = InferenceRule.merge_specialization_maps(my_map_1, my_map_2)
    lines.append(Proof.Line(double_conditional.specialize(my_map).conclusion, double_conditional, []))
    num = len(lines) - 1

    for line in antecedent2_proof.lines:
        assumps = list()
        if not line.is_assumption():
            for ass in line.assumptions:
                assumps.append(ass + num + 1)
            lines.append(Proof.Line(line.formula, line.rule, assumps))
        else:
            lines.append(line)

    lines.append(Proof.Line(double_conditional.specialize(my_map).conclusion.second, MP, [num -1 , num]))
    num = len(lines) - 1
    lines.append(Proof.Line(double_conditional.specialize(my_map).conclusion.second.second, MP, [num -1 , num]))
    my_state = InferenceRule(antecedent1_proof.statement.assumptions, consequent)

    my_rules = antecedent1_proof.rules.union(antecedent2_proof.rules)

    return Proof(my_state, my_rules.union({double_conditional}), lines)



def remove_assumption(proof: Proof) -> Proof:
    """Converts a proof of some `conclusion` formula, the last assumption of
    which is an assumption `assumption`, into a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of ``'(``\ `assumptions`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.4

    working_assumption = proof.statement.assumptions[-1] #last assumption is start of the proof
    my_lines = list()
    implies = '->'

    my_assumptioons = list()
    for ass in proof.statement.assumptions:
        if ass != working_assumption:
            my_assumptioons.append(ass)

    proof_to_newProof = list()


    my_lines.append(Proof.Line(Formula(implies, working_assumption, working_assumption), I0, [])) #first line p->p
    index_ass = len(my_lines) - 1

    for index, line in enumerate(proof.lines):

        # if index == 0:
        #     continue

        if line.formula == working_assumption:
            proof_to_newProof.append(index_ass) #knowing line in proof to the proof to return
            if index != 0:
                my_lines.append(Proof.Line(Formula(implies, working_assumption, working_assumption), I0, []))

        elif line.is_assumption(): #assumption so no rule
            my_lines.append(line)
            to_add = \
                Proof.Line(Formula(implies, line.formula, Formula(implies, working_assumption, line.formula)), I1, [])
            my_lines.append(to_add)
            num = len(my_lines)
            to_add = Proof.Line(Formula(implies, working_assumption, line.formula), MP, [num - 2, num - 1])
            my_lines.append(to_add)
            proof_to_newProof.append(num)

        elif len(line.assumptions) == 0: #rule without assumption
            my_lines.append(line)
            to_add = \
                Proof.Line(Formula(implies, line.formula, Formula(implies, working_assumption, line.formula)), I1, [])
            my_lines.append(to_add)
            num = len(my_lines)
            to_add = Proof.Line(Formula(implies, working_assumption, line.formula), MP, [num - 2, num - 1])
            my_lines.append(to_add)
            proof_to_newProof.append(num)

        else: #has a rule and assumptions
            assumption_in_use = proof.lines[line.assumptions[0]].formula #assumption that the line uses
            first_part = Formula(implies, working_assumption, line.formula)
            scd_part = Formula(implies, Formula(implies, working_assumption, assumption_in_use), first_part)
            d_first = Formula(implies, assumption_in_use, line.formula)
            d_scd = Formula(implies, working_assumption, d_first)
            to_add = Proof.Line(Formula(implies, d_scd, scd_part), D,[])
            my_lines.append(to_add)

            num = len(my_lines)
            to_add = Proof.Line(scd_part, MP, [proof_to_newProof[line.assumptions[1]], num - 1])
            my_lines.append(to_add)

            num = len(my_lines)
            to_add = Proof.Line(first_part, MP, [proof_to_newProof[line.assumptions[0]], num - 1])
            my_lines.append(to_add)
            proof_to_newProof.append(num)


    ccl = Formula(implies, working_assumption, proof.statement.conclusion)
    rules = proof.rules.union({I0, I1, MP, D})
    my_IR = InferenceRule(my_assumptioons, ccl)

    return Proof(my_IR, rules, my_lines)


def proof_from_inconsistency(proof_of_affirmation: Proof,
                             proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6

    return combine_proofs(proof_of_negation, proof_of_affirmation, conclusion, I2)

def prove_by_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, into a proof of `formula` from
    the same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7

    working_proof = remove_assumption(proof)
    i0_in_use = working_proof.statement.conclusion.second.first # p->p

    last_assump = proof.statement.assumptions[-1] #ccl from proof ~r
    first_part = Formula("->", i0_in_use, last_assump.first)
    scd_part = Formula("->", working_proof.statement.conclusion, first_part)

    my_lines = list()

    for line in working_proof.lines:
        my_lines.append(line)

    #adding the lines we need
    my_lines.append(Proof.Line(scd_part, N, []))
    num = len(my_lines) - 1
    my_lines.append(Proof.Line(first_part, MP, [num - 1, num]))
    my_lines.append(Proof.Line(i0_in_use, I0, []))
    num = len(my_lines) - 1
    my_lines.append(Proof.Line(last_assump.first, MP, [num, num - 1]))

    my_rules = { MP, I0, I1, D, N, NI} # NI ? added for the test

    assumps = list()
    for i in range(len(proof.statement.assumptions)): #without the last one
        if i != len(proof.statement.assumptions) - 1:
            assumps.append(proof.statement.assumptions[i])

    my_statement = InferenceRule(assumps, last_assump.first)

    return Proof(my_statement, my_rules, my_lines)