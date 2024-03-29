# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/completeness.py

from typing import AbstractSet, Container, Set, Union

from logic_utils import fresh_constant_name_generator

from predicates.syntax import *
from predicates.semantics import *
from predicates.proofs import *
from predicates.prover import *
from predicates.deduction import *
from predicates.prenex import *

from itertools import product

def get_constants(formulas: AbstractSet[Formula]) -> Set[str]:
    """Finds all constant names in the given formulas.

    Parameters:
        formulas: formulas to find all constant names in.

    Returns:
        A set of all constant names used in one or more of the given formulas.
    """
    constants = set()
    for formula in formulas:
        constants.update(formula.constants())
    return constants

def is_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if the given set of sentences is primitively, universally, and
        existentially closed, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    return is_primitively_closed(sentences) and \
           is_universally_closed(sentences) and \
           is_existentially_closed(sentences)

def is_primitively_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    primitively closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every n-ary relation name from the given sentences, and
        for every n (not necessarily distinct) constant names from the given
        sentences, either the invocation of this relation name over these
        constant names (in order), or the negation of this invocation, is one of
        the given sentences, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1.1

    consts = set() #get_constants defonce le run time
    relations = set()
    for sentence in sentences:
        consts.update(sentence.constants())
        relations.update(sentence.relations())

    for rel in relations:

        perms = product(consts, repeat=rel[1])

        for perm in perms:

            str_ = str(rel[0]) + '('

            for arg in perm:
                str_ += str(arg)
                str_ += ","

            str_ = str_[:-1]
            str_ += ")"

            rel_not_neg = str_
            neg = "~" + str_
            flag = False

            for form in sentences:

                if rel_not_neg == str(form) or neg == str(form): #searching just for one to be true
                    flag = True
                    break

            if not flag:
                return False


    return True


def is_universally_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    universally closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every universally quantified sentence of the given
        sentences, and for every constant name from the given sentences, the
        predicate of this quantified sentence, with every free occurrence of the
        universal quantification variable replaced with this constant name, is
        one of the given sentences, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1.2

    consts = get_constants(sentences)
    # for sentence in sentences:
    #     consts.update(sentence.constants())


    for sentence in sentences:
        if sentence.root == "A":
            for const in consts:
                sub = {sentence.variable : Term(const)}
                formula = sentence.predicate.substitute(sub)
                if not formula in sentences:
                    return False

    return True



def is_existentially_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    existentially closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every existentially quantified sentence of the given
        sentences there exists a constant name such that the predicate of this
        quantified sentence, with every free occurrence of the existential
        quantification variable replaced with this constant name, is one of the
        given sentences, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1.3

    consts = get_constants(sentences)
    # for sentence in sentences:
    #     consts.update(sentence.constants())


    for sentence in sentences:

        if sentence.root == "E":

            flag = False
            for const in consts:
                sub = {sentence.variable : Term(const)}
                formula = sentence.predicate.substitute(sub)
                if formula in sentences:
                    flag = True
                    break

            if not flag:
                return False

    return True


def find_unsatisfied_quantifier_free_sentence(sentences: Container[Formula],
                                              model: Model[str],
                                              unsatisfied: Formula) -> Formula:
    """
    Given a closed set of prenex-normal-form sentences, given a model whose
    universe is the set of all constant names from the given sentences, and
    given a sentence from the given set that the given model does not satisfy,
    finds a quantifier-free sentence from the given set that the given model
    does not satisfy.

    Parameters:
        sentences: closed set of prenex-normal-form sentences, which is only to
            be accessed using containment queries, i.e., using the ``in``
            operator as in:

            >>> if sentence in sentences:
            ...     print('contained!')

        model: model for all element names from the given sentences, whose
            universe is `get_constants`\ ``(``\ `sentences`\ ``)``.
        unsatisfied: sentence (which possibly contains quantifiers) from the
            given sentences that is not satisfied by the given model.

    Returns:
        A quantifier-free sentence from the given sentences that is not
        satisfied by the given model.
    """
    # We assume that every sentence in sentences is of type formula, is in
    # prenex normal form, and has no free variables, and furthermore that the
    # set of constants that appear somewhere in sentences is model.universe;
    # but we cannot assert these since we cannot iterate over sentences.
    for constant in model.universe:
        assert is_constant(constant)
    assert is_in_prenex_normal_form(unsatisfied)
    assert len(unsatisfied.free_variables()) == 0
    assert unsatisfied in sentences
    assert not model.evaluate_formula(unsatisfied)
    # Task 12.2

    # Base case - No quantifier
    if is_quantifier_free(unsatisfied):
        return unsatisfied


    consts = model.universe


    for const in consts:

        const = Term(const)

        if is_quantifier(unsatisfied.root):

            after_sub = unsatisfied.predicate.substitute({unsatisfied.variable : const})

            if not model.evaluate_formula(after_sub) and after_sub in sentences:

                return find_unsatisfied_quantifier_free_sentence(sentences, model, after_sub)


def get_primitives(quantifier_free: Formula) -> Set[Formula]:
    """Finds all primitive subformulas of the given quantifier-free formula.

    Parameters:
        quantifier_free: quantifier-free formula whose subformulas are to
            be searched.

    Returns:
        The primitive subformulas (i.e., relation invocations) of the given
        quantifier-free formula.

    Examples:
        The primitive subformulas of ``'(R(c1,d)|~(Q(c1)->~R(c2,a)))'`` are
        ``'R(c1,d)'``, ``'Q(c1)'``, and ``'R(c2,a)'``.
    """
    assert is_quantifier_free(quantifier_free)
    # Task 12.3.1

    rel = set()

    if is_relation(quantifier_free.root):
        rel.add(quantifier_free)

    else:
        rel.update(get_primitives(quantifier_free.first))

        if is_binary(quantifier_free.root):
            rel.update(get_primitives(quantifier_free.second))

    return rel


def model_or_inconsistency(sentences: AbstractSet[Formula]) -> \
        Union[Model[str], Proof]:
    """Either finds a model in which the given closed set of prenex-normal-form
    sentences holds, or proves a contradiction from these sentences.

    Parameters:
        sentences: closed set of prenex-normal-form sentences to either find a
            model for or prove a contradiction from.

    Returns:
        A model in which all of the given sentences hold if such exists,
        otherwise a valid proof of  a contradiction from the given formulas via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_closed(sentences)
    # Task 12.3.2
    relations = set()
    my_dict = {}
    for sentence in sentences :

        if is_relation(sentence.root):
            relations.add(sentence)
            my_dict[sentence.root] = set()



    for relation in relations:
        all_const = my_dict[relation.root]
        all_const.add(tuple(r.root for r in relation.arguments))
        my_dict[relation.root] = all_const

    c_meaning = dict()
    constants = get_constants(sentences)
    for cons in constants:
        c_meaning[cons] = cons

    my_model = Model(constants, c_meaning, my_dict )
    if my_model.is_model_of(sentences):
        return my_model


    for sentence in sentences:
        if not my_model.evaluate_formula(sentence):
            free_quantifiers = find_unsatisfied_quantifier_free_sentence(sentences , my_model , sentence)
            primitives = get_primitives(free_quantifiers)
            my_lst = list()

            for prim in primitives:
                if prim in sentences:
                    my_lst.append(str(prim))
                else:
                    my_lst.append(Formula("~" , prim))

            my_lst.append(free_quantifiers)
            prover = Prover(Prover.AXIOMS.union(my_lst))

            lines = list()

            for ass in my_lst:
                step = prover.add_assumption(ass)
                lines.append(step)
            step1 = prover.add_tautological_implication(Formula("~" , free_quantifiers) , lines)
            step2 = prover.add_assumption(free_quantifiers)
            prover.add_tautological_implication(Formula("&" , free_quantifiers , Formula("~" , free_quantifiers)) ,[step2, step1])
            return prover.qed()
    return my_model



def combine_contradictions(proof_from_affirmation: Proof,
                           proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs of contradictions, both from the same
    assumptions/axioms except that the latter has an extra assumption that is
    the negation of an extra assumption that the former has, into a single proof
    of a contradiction from only the common assumptions/axioms.

    Parameters:
        proof_from_affirmation: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        proof_from_negation: valid proof of a contradiction from the same
            assumptions/axioms of `proof_from_affirmation`, but with one
            simple assumption `assumption` replaced with its negation
            ``'~``\ `assumption` ``'``.

    Returns:
        A valid proof of a contradiction from only the assumptions/axioms common
        to the given proofs (i.e., without `assumption` or its negation).
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    common_assumptions = proof_from_affirmation.assumptions.intersection(
        proof_from_negation.assumptions)
    assert len(common_assumptions) == \
           len(proof_from_affirmation.assumptions) - 1
    assert len(common_assumptions) == len(proof_from_negation.assumptions) - 1
    affirmed_assumption = list(
        proof_from_affirmation.assumptions.difference(common_assumptions))[0]
    negated_assumption = list(
        proof_from_negation.assumptions.difference(common_assumptions))[0]
    assert len(affirmed_assumption.templates) == 0
    assert len(negated_assumption.templates) == 0
    assert negated_assumption.formula == \
           Formula('~', affirmed_assumption.formula)
    assert proof_from_affirmation.assumptions.issuperset(Prover.AXIOMS)
    assert proof_from_negation.assumptions.issuperset(Prover.AXIOMS)
    for assumption in common_assumptions.union({affirmed_assumption,
                                                negated_assumption}):
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.4

    # aff_assumptions = list(proof_from_affirmation.assumptions)
    # neg_assumptions = list(proof_from_negation.assumptions)

    affirmation_proof = proof_by_way_of_contradiction(proof_from_affirmation , affirmed_assumption.formula)

    negation_proof = proof_by_way_of_contradiction(proof_from_negation , negated_assumption.formula)

    contradiction_to_prove = str(Formula("&" , affirmation_proof.conclusion , negation_proof.conclusion))

    prover = Prover(affirmation_proof.assumptions)

    step1 = prover.add_proof(affirmation_proof.conclusion , affirmation_proof)
    step2 = prover.add_proof(negation_proof.conclusion , negation_proof)

    prover.add_tautological_implication(contradiction_to_prove, [step1 , step2])

    return prover.qed()


def eliminate_universal_instantiation_assumption(proof: Proof, constant: str,
                                                 instantiation: Formula,
                                                 universal: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `universal` and `instantiation`, where the latter is a universal
    instantiation of the former, to a proof of a contradiction from the same
    assumptions without `instantiation`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        universal: assumption of the given proof that is universally quantified.
        instantiation: assumption of the given proof that is obtained from the
            predicate of `universal` by replacing all free occurrences of the
            universal quantification variable by some constant.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `instantiation`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(instantiation) in proof.assumptions
    assert Schema(universal) in proof.assumptions
    assert universal.root == 'A'
    assert instantiation == \
           universal.predicate.substitute({universal.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.5

    affirmation_p = proof_by_way_of_contradiction(proof, instantiation)

    prover = Prover(affirmation_p.assumptions)
    step1 = prover.add_proof(affirmation_p.conclusion, affirmation_p)
    step2 = prover.add_assumption(universal)
    step3 = prover.add_universal_instantiation(instantiation, step2, constant)

    form = Formula("&", instantiation, Formula("~", instantiation))

    prover.add_tautological_implication(form, [step3, step1])

    return prover.qed()



def universal_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with all universal instantiations of each
    universally quantified sentence from these sentences, with respect to all
    constant names from these sentences.

    Parameters:
        sentences: prenex-normal-form sentences to augment with their universal
            instantiations.

    Returns:
        A set of all of the given sentences, and in addition any formula that
        can be obtained replacing in the predicate of any universally quantified
        sentence from the given sentences, all occurrences of the quantification
        variable with some constant from the given sentences.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.6

    constants = get_constants(sentences)

    new_sentences = set()

    for sentence in sentences:

        new_sentences.add(sentence)

        if sentence.root == "A":

            for const in constants:

                new_sentences.add(sentence.predicate.substitute({sentence.variable:Term(const)}))

        # else:
        #     new_sentences.add(sentence)

    return new_sentences




def replace_constant(proof: Proof, constant: str, variable: str = 'zz') -> \
        Proof:
    """Replaces all occurrences of the given constant in the given proof with
    the given variable.

    Parameters:
        proof: a valid proof.
        constant: a constant name that does not appear as a template constant
            name in any of the assumptions of the given proof.
        variable: a variable name that does not appear anywhere in given the
            proof or in its assumptions.

    Returns:
        A valid proof where every occurrence of the given constant name in the
        given proof and in its assumptions is replaced with the given variable
        name.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert is_variable(variable)
    for assumption in proof.assumptions:
        assert constant not in assumption.templates
        assert variable not in assumption.formula.variables()
    for line in proof.lines:
        assert variable not in line.formula.variables()
    # Task 12.7.1

    map = {constant: Term(variable)}

    assumps = set()
    for assumption in proof.assumptions:
        assumps.add(Schema(assumption.formula.substitute(map), assumption.templates))

    prover = Prover(assumps)

    for line in proof.lines:

        if constant in line.formula.constants():
            form = line.formula.substitute(map)

            if isinstance(line, Proof.AssumptionLine):

                instantiation_map = dict()

                all = line.instantiation_map.items()

                for key, value in all:
                    if type(value) is str:
                        instantiation_map[key] = value
                    else:
                        instantiation_map.update({key: value.substitute(map)})

                prover.add_instantiated_assumption(form, line.assumption, instantiation_map)

            elif isinstance(line, Proof.UGLine):
                prover.add_ug(form, line.predicate_line_number)

            elif isinstance(line, Proof.TautologyLine):
                prover.add_tautology(form)

            elif isinstance(line, Proof.MPLine):
                prover.add_mp(form, line.antecedent_line_number, line.conditional_line_number)

        else:
            prover._add_line(line)

    return prover.qed()


def eliminate_existential_witness_assumption(proof: Proof, constant: str,
                                             witness: Formula,
                                             existential: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `existential` and `witness`, where the latter is an existential
    witness of the former, to a proof of a contradiction from the same
    assumptions without `witness`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        existential: assumption of the given proof that is existentially
            quantified.
        witness: assumption of the given proof that is obtained from the
            predicate of `existential` by replacing all free occurrences of the
            existential quantification variable by some constant that does not
            appear in any assumption of the given proof except for this
            assumption.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `witness`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(witness) in proof.assumptions
    assert Schema(existential) in proof.assumptions
    assert existential.root == 'E'
    assert witness == \
           existential.predicate.substitute(
               {existential.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    for assumption in proof.assumptions.difference({Schema(witness)}):
        assert constant not in assumption.formula.constants()
    # Task 12.7.2

    replaced = replace_constant(proof, constant, 'zz')
    form = witness.substitute({constant:Term("zz")})


    proof1 = proof_by_way_of_contradiction(replaced, form)
    prover = Prover(proof1.assumptions)
    step1 = prover.add_proof(proof1.conclusion, proof1)

    form1 = Formula("~", form)
    map2 = {"zz": Term(existential.variable)}
    step2 = prover.add_free_instantiation(form1.substitute(map2), step1, map2)

    form3 = Formula('->', form1.substitute(map2).first, Formula('&', form, form1))
    step3 = prover.add_tautological_implication(form3, {step2})

    step4 = prover.add_assumption(existential)
    prover.add_existential_derivation(Formula('&', form, form1), step4, step3)


    return prover.qed()

def existential_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with an existential witness that uses a new
    constant name, for each existentially quantified sentences from these
    sentences for which an existential witness is missing.

    Parameters:
        sentences: prenex-normal-form sentences to augment with any missing
            existential witnesses.

    Returns:
        A set of all of the given sentences, and in addition for every
        existentially quantified sentence from the given sentences, a formula
        obtained from the predicate of that quantified sentence by replacing all
        occurrences of the quantification variable with a new constant name
        obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_constant_name_generator`\ ``)``.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.8

    my_sentences = list(sentences)
    const = list()
    for cst in get_constants(sentences):

        const.append(Term(cst))

    for sen in sentences :

        if sen.root == 'E':

            flag = False

            for consta in const :
                if sen.predicate.substitute({sen.variable:consta}) in sentences:
                    flag = True
                    break

            if not flag :
                consta = Term(next(fresh_constant_name_generator))

                my_sentences.append(sen.predicate.substitute({sen.variable:consta}))

    return set(my_sentences)
