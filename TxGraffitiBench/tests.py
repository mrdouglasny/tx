import numpy as np
import networkx as nx
import graphcalc as gc

# Invariants that take in a single graph
# (will add to this)
invariants_to_test = np.array([
    gc.clique_number, gc.independence_number, gc.chromatic_number
    ])
vectorized_invariants = [np.vectorize(f) for f in invariants_to_test]

# A large collection of test graphs
path_graph_sizes = [1, 2, 3, 4, 5]
path_graphs = [nx.path_graph(i) for i in path_graph_sizes]

cycle_graph_sizes = [1, 2, 3, 4, 5]
cycle_graphs = [nx.cycle_graph(i) for i in cycle_graph_sizes]
graphs = np.array(path_graphs + cycle_graphs, dtype=object)

# WH: Maybe I can make this a fancier dataframe
# We can also output the results to a file so we only
# have to generate this once; (running all the functions on many graphs
# may take a while).
results = [f(graphs) for f in vectorized_invariants]
# [array([1, 2, 2, 2, 2, 1, 2, 3, 2, 2]),
#  array([1, 1, 2, 2, 3, 0, 1, 1, 2, 2]),
#  array([1, 2, 2, 2, 2, 1, 2, 3, 2, 3])]
