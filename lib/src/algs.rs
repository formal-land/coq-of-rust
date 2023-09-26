use std::collections::{HashMap, HashSet};

type DirectedGraph<K> = HashMap<K, HashSet<K>>;

/// changes the direction of edges in a given directed graph
pub(crate) fn reverse_graph<K>(graph: DirectedGraph<K>) -> DirectedGraph<K>
where
    K: core::clone::Clone + std::cmp::Eq + std::hash::Hash,
{
    let mut reversed = HashMap::new();

    for (src, dests) in graph {
        for dest in dests {
            reversed
                .entry(dest)
                .or_insert(HashSet::new())
                .insert(src.clone());
        }
    }

    reversed
}
