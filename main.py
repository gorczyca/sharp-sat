"""This script calculates the solution of the #SAT problem given an instance.

Requirements:
    input file - SAT formula in CNF DIMACS with path specified in the global variable INPUT_PATH
    anytree - python module for tree data structures (installed via 'pip install anytree'
    tree decomposer - executable file that can be used from terminal with a parameter specifying input graph file:
        e.g.: ./out/htd_main - htd_main executable in the ./out/ directory relative to this script file.
"""

import subprocess
from typing import Tuple, List, TextIO, Dict

from anytree import Node, RenderTree, PostOrderIter


SAT_DESCRIPTION_CHAR = 'p'
COMMENT_CHAR = 'c'
ENDLINE_CHAR = '0'
WEIGHT_CHAR = 'w'
BAG_SYMBOL = 'b'
TD_DESCRIPTION_CHAR = 's'
TW_SYMBOL = 'tw'

ROOT_ID = 1

INPUT_PATH = './examples/sat.dimacs'
PRIMAL_GRAPH_OUTPUT_PATH = './out/graph.td'

BASH_COMMAND = './out/htd_main --instance {}'


def parse_file(file_path: str) -> Tuple[List[List[int]], int, int, Dict[int, float]]:
    """Parses input SAT formula in CNF format.

    :param file_path: Input file path.
    :return: tuple(clauses, variables_count, clauses_count, weights)
        WHERE
        clauses: list of clauses, represented as a list of ints
        variables_count: number of variables in formula
        clauses_count: number of clauses in a formula
        weights: a dictionary of weight for each formula (for weighted model counting problem)
    """
    clauses = []
    with open(file_path, 'r') as input_file:
        variables_count = 0
        clauses_count = 0
        weights = {}
        for line in input_file:
            characters = line.split()
            if characters[0] == COMMENT_CHAR:
                pass
            elif characters[0] == SAT_DESCRIPTION_CHAR:
                variables_count = int(characters[2])
                clauses_count = int(characters[3])
            elif characters[0] == WEIGHT_CHAR:
                weights[int(characters[1])] = float(characters[2])
            else:
                clause = [int(var) for var in characters if var != ENDLINE_CHAR]
                clauses.append(sorted(clause))
        input_file.close()
        return clauses, variables_count, clauses_count, weights


def create_primal_graph_file(clauses: List[List[int]], variables_count: int,
                             output_file_path: str = PRIMAL_GRAPH_OUTPUT_PATH) -> TextIO:
    """Creates a file with primal graph representation of the SAT formula in CNF DIMACS.

    :param clauses: list of clauses, represented as a list of ints
    :param variables_count: number of variables in formula (number of nodes of the primal graph)
    :param output_file_path: path of the output file
    :return: output file with SAT primal graph encoding
    """
    edges = set()
    cliques = [[abs(var) for var in clause] for clause in clauses]
    for clique in cliques:
        for var1 in clique:
            var1_edges = [(var1, var2) for var2 in clique if var1 < var2]
            if var1_edges:
                edges.update(var1_edges)

    dimacs_graph_string = f'{SAT_DESCRIPTION_CHAR} {TW_SYMBOL} {variables_count} {len(edges)}\n'
    dimacs_graph_string += '\n'.join([f'{edge[0]} {edge[1]}' for edge in edges])
    with open(output_file_path, 'w') as output_file:
        output_file.write(dimacs_graph_string)
        output_file.close()
        return output_file


def get_tree_decomposition(input_file_name: str) -> Tuple[Dict[int, Node], int, int, int]:
    """Creates the tree decomposition of the primal graph, based on its representation in the text file.
    It uses an external tree-decomposer (see description on the top of the file)

    :param input_file_name: Path to the input file with graph's representation (should have a *.td extension)
    :return:    tuple(nodes, bags_count, treewidth, variables_count)
                WHERE
                nodes: dictionary <id of the node (bag)>: <node> of the created tree decomposition
                nodes_count: number of nodes (bags)
                treewidth: width of the tree decomposition
                variables_count: number of variables in tree decomposition (number of nodes of the primal graph)
    """
    bash_command = BASH_COMMAND.format(input_file_name)
    process = subprocess.Popen(bash_command.split(), stdout=subprocess.PIPE)
    output, error = process.communicate()

    nodes: Dict[int, Node] = {}
    nodes_count = 0
    treewidth = 0
    variables_count = 0
    edges = set()
    for line in str(output.decode()).split('\n'):
        line_characters = line.split()
        if not line_characters:
            continue
        if line_characters[0] == TD_DESCRIPTION_CHAR:
            nodes_count = int(line_characters[2])
            treewidth = int(line_characters[3])
            variables_count = int(line_characters[4])
        elif line_characters[0] == BAG_SYMBOL:
            id_ = int(line_characters[1])
            bag = list(map(int, line_characters[2:]))
            node = Node(id_, bag=bag, assignments=None)
            nodes[id_] = node
        else:
            edges.add(tuple(map(int, line_characters)))

    for edge in edges:
        child_id = edge[1]
        parent_id = edge[0]
        nodes[child_id].parent = nodes[parent_id]

    return nodes, nodes_count, treewidth, variables_count


def get_bag_clauses(bag: List[int], clauses: List[List[int]]) -> List[List[int]]:
    """Returns the formula clauses that the bag (of variables) covers.

    :param bag: Set of variables.
    :param clauses: Set of all clauses of the SAT formula.
    :return: Subset of the set of clauses, that contains only variables from bag.
    """
    bag_clauses = []
    for clause in clauses:
        abs_clause = set([abs(var) for var in clause])
        if abs_clause.issubset(bag):
            bag_clauses.append(clause)
    return bag_clauses


def evaluates_to_true(truth_assignment: bool, positive: bool):
    """Evaluates the truth_assignment (False or True) based on whether the literal is positive or not.
    :param truth_assignment: Variable truth assignment.
    :param positive: True if literal is positive; False otherwise.
    :return: Evaluation
    """
    return truth_assignment == positive


def str_to_bool(assignment_char: str) -> bool:
    """Maps a string of '0' or '1' to False or True respectively.
    :param assignment_char: Variable assignment ('0' or '1')
    :return: Mapping of the assignment_char to False or True
    """
    return bool(int(assignment_char))


def satisfies_clause(assignment, clause, variables) -> bool:
    """Returns True if assignment evaluates clause to true; False otherwise.

    :param assignment:  Variable assignment in a string form, where '0' represents False and '1' represents True,
                        for every variable in the set 'variables'.
    :param clause: Clause to check whether it's satisfied by the assignment.
    :param variables: List of variables, that are assigned by the 'assignment'.
    :return: True if assignment evaluates clause to true; False otherwise
    """
    for var in clause:
        var_index = variables.index(abs(var))
        if evaluates_to_true(str_to_bool(assignment[var_index]), var > 0):
            return True     # it's enough to evaluate only one variable to true
    return False


def matches(assignment_1, variables_1, assignment_2, variables_2):
    """Checks whether 'assignment_1' and 'assignment_2' agrees on the intersection of the sets 'variables_1'
    and 'variables_2'.

    :param assignment_1: First truth assignment
    :param variables_1: Variables mapped by the first truth assignment.
    :param assignment_2: Second truth assignment.
    :param variables_2: Variables mapped by the second truth assignment.
    :return: True if 'assignment_1' and 'assignment_2' match w.r.t. the intersection of their variables;
             False otherwise.
    """
    matching_variables = list(set(variables_1) & set(variables_2))
    for var in matching_variables:
        assingment_1_var_index = variables_1.index(var)
        assingment_2_var_index = variables_2.index(var)
        if assignment_1[assingment_1_var_index] != assignment_2[assingment_2_var_index]:
            return False
    return True


def get_assignments_count(assignment, variables, children_nodes):
    """Returns the number of satisfying assignments of non-leaf node of the tree decomposition.

    :param assignment: An assignment
    :param variables: Variable of the 'assignment'.
    :param children_nodes: Children of the node containing 'assignment'.
    :return: Number of satisfying assignments
    """
    matches_count = 1
    for child in children_nodes:
        child_assignment_count = 0
        for child_assignment in child.assignments:
            if matches(assignment, variables, child_assignment[0], child.bag):
                child_assignment_count += child_assignment[1]
        matches_count *= child_assignment_count
    return matches_count


def get_satisfying_assignments_with_cardinality(variables: List[int], bag_clauses: List[List[int]]) \
        -> List[Tuple[str, int]]:
    """Returns a list of tuples(assignment, cardinality) satisfying clauses ('bag_clauses'),
    where assignment is a string representing the truth assignment in binary, e.g. '01001' -> False, True, False, False, True.

    :param variables: List of variables appearing in the clauses.
    :param bag_clauses: Clauses of the SAT formula covered by 'variables'.
    :return: List of tuples(assignment, cardinality).
    """
    variables_count = len(variables)
    satisfying_assignments = set()
    for i in range(2**variables_count):
        assignment = format(i, f'0{variables_count+2}b')[2:]
        satisfies_all_bag_clauses = True
        for bag_clause in bag_clauses:
            if not satisfies_clause(assignment, bag_clause, variables):
                satisfies_all_bag_clauses = False
                break
        if satisfies_all_bag_clauses:
            satisfying_assignments.add(assignment)

    assignments_with_cardinality = []
    if node.children:
        for assignment in satisfying_assignments:
            assignment_matches_count = get_assignments_count(assignment, node.bag, node.children)
            if assignment_matches_count > 0:
                assignments_with_cardinality.append((assignment, assignment_matches_count))
    else:
        assignments_with_cardinality = [(assignment, 1) for assignment in satisfying_assignments]

    return assignments_with_cardinality


def get_total_assignment_count(root_node: Node):
    """Calculates total number of satisfying assignments - solution of the #SAT problem.

    :param root_node: Root of the tree decomposition.
    :return: Number of satisfying assignment.
    """
    total_count = 0
    for _, count in root_node.assignments:
        total_count += count
    return total_count


if __name__ == '__main__':
    cls, var_count, _, _ = parse_file(INPUT_PATH)
    primal_graph_file = create_primal_graph_file(cls, var_count)
    nodes, _, _, _ = get_tree_decomposition(primal_graph_file.name)
    root = nodes[ROOT_ID]

    for node in PostOrderIter(root):
        bag_cls = get_bag_clauses(node.bag, cls)
        assignments = get_satisfying_assignments_with_cardinality(node.bag, bag_cls)
        node.assignments = assignments

    for pre, fill, node in RenderTree(root):
        print(f'{pre}{node.name}: {node.bag} { {assignment:  count for assignment, count in node.assignments} }')

    print(f'Total number of satisfying assignments: {get_total_assignment_count(root)}')
