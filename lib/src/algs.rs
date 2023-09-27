use std::collections::{HashMap, HashSet, VecDeque};

type DirectedGraph<V> = HashMap<V, HashSet<V>>;

pub(crate) fn find_last<V>(start: V, graph: DirectedGraph<V>) -> V
where
    V: core::clone::Clone + std::cmp::Eq + std::hash::Hash,
{
    let mut current_last = &start;
    let mut queue = VecDeque::new();

    while let Some(vertices) = graph.get(current_last) {
        for v in vertices {
            queue.push_back(v);
        }
        if let Some(new_last) = queue.pop_front() {
            current_last = new_last;
        } else {
            break;
        }
    }

    current_last.to_owned()
}

/// changes the direction of edges in a given directed graph
pub(crate) fn reverse_graph<V>(graph: DirectedGraph<V>) -> DirectedGraph<V>
where
    V: core::clone::Clone + std::cmp::Eq + std::hash::Hash,
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

#[inline]
pub(crate) fn to_set<A>(v: &[A]) -> HashSet<A>
where
    A: core::clone::Clone + std::cmp::Eq + std::hash::Hash,
{
    v.into_iter().map(|x| x.to_owned()).collect()
}
