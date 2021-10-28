# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""



from typing import AbstractSet, Iterable, Iterator, List, Mapping

from propositions.syntax import *
from propositions.proofs import *
import itertools

Model = Mapping[str, bool]
SEPARATOR = "|"

def is_model(model: Model) -> bool:
    """Checks if the given dictionary a model over some set of variables.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variables,
        ``False`` otherwise.
    """
    for key in model:
        if not (is_variable(key) and type(model[key]) is bool):
            return False
    return True

def variables(model: Model) -> AbstractSet[str]:
    """Finds all variables over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variables over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()

def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variables of the formula,
            to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    # Task 2.1
    if is_variable(formula.__repr__()): #checking if just a variable
        return model[formula.root]

    if is_constant(formula.__repr__()):
        if formula.root == "T": #checking the value
            return True
        return False

    if is_unary(formula.root):
        return not evaluate(formula.first, model)

    if is_binary(formula.root):
        if formula.root == "|":
            return (evaluate(formula.first, model) or evaluate(formula.second, model))
        if formula.root == "&":
            return (evaluate(formula.first, model) and evaluate(formula.second, model))
        if formula.root == "->": # "->" operator
            first_bool = evaluate(formula.first, model)
            secd_bool = evaluate(formula.second, model)

            if not first_bool or secd_bool :
                return True
            return False
        if formula.root == "-|":
            return not (evaluate(formula.first, model) or evaluate(formula.second, model))
        if formula.root == "-&":
            return not (evaluate(formula.first, model) and evaluate(formula.second, model))
        if formula.root == "+":
            first_bool = evaluate(formula.first, model)
            secd_bool = evaluate(formula.second, model)

            if (not first_bool and secd_bool) or (first_bool and not secd_bool):
                return True
            return False
        if formula.root == "<->":
            first_bool = evaluate(formula.first, model)
            secd_bool = evaluate(formula.second, model)

            if (first_bool and secd_bool) or (not first_bool and not secd_bool):
                return True
            return False


def all_models(variables: List[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variables.

    Parameters:
        variables: list of variables over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variables. The order
        of the models is lexicographic according to the order of the given
        variables, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]
    """
    for v in variables:
        assert is_variable(v)
    # Task 2.2
    list_dicts = list()
    my_list = [False, True]
    combinations = list(itertools.product(my_list, repeat = len(variables)))
    for combi in combinations:
        dict_combi = dict()
        index = 0
        for var in variables :
            dict_combi[var] = combi[index]
            index += 1
        index = 0
        list_dicts.append(dict_combi)
        dict_combi = dict()
    return list_dicts




def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.
    """
    # Task 2.3
    bool_list = list()
    for model in models :
        bool_list.append(evaluate(formula, model))
    return bool_list

def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    # Task 2.4
    str_print = ""
    flag_first = False
    variables = sorted(list(formula.variables()))
    for var in variables:
        str_print += (SEPARATOR + " " + var + " ")
    str_print += (SEPARATOR + " " + formula.__repr__() + " " + SEPARATOR + "\n")
    for var in formula.variables():
        str_print += (SEPARATOR + "-"*(len(var) + 2))
    str_print += (SEPARATOR + "-"*(len(formula.__repr__()) + 2) + SEPARATOR + "\n")
    models = all_models(variables)
    for model in models:
        if flag_first:
            str_print += "\n"
        bool_answer = evaluate(formula, model)
        for var in variables :
            str_print += SEPARATOR + " "
            if model[var]:
                str_print += "T"
            else :
                str_print += "F"
            str_print += " " * len(var)
        str_print += SEPARATOR + " "
        if bool_answer:
            str_print += "T"
        else:
            str_print += "F"
        str_print += " " * len(formula.__repr__()) + SEPARATOR
        flag_first = True
    print(str_print)



def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    # Task 2.5a
    truth_table = truth_values(formula, all_models(formula.variables()))
    for val in truth_table:
        if not val :
            return False
    return True

def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    # Task 2.5b
    return not is_satisfiable(formula)


def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    # Task 2.5c
    truth_table = truth_values(formula, all_models(formula.variables()))
    for val in truth_table:
        if val :
            return True
    return False

def __create_dnf__(forms):

    if len(forms) == 1:
        return forms[0]
    return Formula("&", forms[0], __create_dnf__(forms[1:]))


def synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single clause that
      evaluates to ``True`` in the given model, and to ``False`` in any other
      model over the same variables.

    Parameters:
        model: model in which the synthesized formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    # Task 2.6
    forms = list()
    for var in model:
        if not model[var]:
            forms.append(Formula("~", Formula(var)))
        else :
            forms.append(Formula(var))
    return __create_dnf__(forms)

def __create_cnf__(forms):

    if len(forms) == 1:
        return forms[0]
    return Formula("|", forms[0], __create_cnf__(forms[1:]))

def synthesize(variables: List[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variables, from
    the given specification of which value the formula should have on each
    possible model over these variables.

    Parameters:
        variables: the set of variables for the synthesize formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Task 2.7

    options = all_models(variables)
    forms = list()
    index = 0
    bool_flag = True #If only false values
    for val in values:
        if val:
            bool_flag = False
            forms.append(synthesize_for_model(options[index]))
        index += 1

    if bool_flag : #Only false values return an always false formula
        return Formula("&",Formula(variables[0]), Formula("~", Formula(variables[0])))  # (x&~x) false formula

    return __create_cnf__(forms)

# Tasks for Chapter 4

def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.
    """
    assert is_model(model)
    # Task 4.2

    false_flag = False

    for assump in rule.assumptions:

        assump = Formula.parse_prefix(str(assump))[0] #Check if a formula is given

        if assump not in model:
            to_check = evaluate(assump, model)

        else:
            to_check = model[str(assump)]

        if to_check == False :
            false_flag = True


    ccl = Formula.parse_prefix(str(rule.conclusion))[0]  # Check if a formula is given

    if ccl not in model:
        ccl_to_check = evaluate(rule.conclusion, model)

    else:
        ccl_to_check = model[str(rule.conclusion)]

    if ccl_to_check == False and not false_flag:
        return False

    return True

def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3

    if len(rule.assumptions) == 0:
        return is_tautology(rule.conclusion)


    for model in all_models(rule.variables()):
        bool_flag = evaluate_inference(rule, model)
        if not bool_flag:
            return False
    return True
