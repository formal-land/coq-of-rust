use std::collections::{HashMap, HashSet, VecDeque};
use topological_sort::TopologicalSort;

/// a type of directed graphs
pub(crate) struct DirectedGraph<V>(HashMap<V, HashSet<V>>);

impl<V> DirectedGraph<V>
where
    V: std::clone::Clone + std::cmp::Eq + std::hash::Hash,
{
    pub(crate) fn of_hashmap(hm: &HashMap<V, HashSet<V>>) -> Self {
        DirectedGraph(hm.to_owned())
    }

    /// if `graph` is a directed acyclic graph,
    /// creates a subgraph with all descendants of `starts`
    pub(crate) fn get_subgraph_of(&self, start: &V) -> DirectedGraph<V> {
        let mut result = HashMap::new();
        let mut queue = VecDeque::new();
        queue.push_back(start);

        while let Some(vertex) = queue.pop_front() {
            if let Some(succs) = self.0.get(vertex) {
                result.entry(vertex.clone()).or_insert(succs.clone());

                for succ in succs {
                    queue.push_back(succ)
                }
            }
        }

        DirectedGraph(result)
    }

    /// topologically sort the graph
    pub(crate) fn to_topological_sort(&self) -> TopologicalSort<V> {
        self.0
            .iter()
            .fold(&mut TopologicalSort::new(), |result, (prec, succs)| {
                succs.iter().fold(result, |result, succ| {
                    result.add_dependency(succ.to_owned(), prec.to_owned());
                    result
                })
            })
            .clone()
    }
}
/*#[inline]
/// assigns `new` to `*old` if `*old < new`
fn assign_if_greater<A>(old: &mut A, new: A)
where
    A: std::cmp::PartialOrd,
{
    if *old < new {
        *old = new
    }
}

pub(crate) fn longest_paths_length<'a, V>(start: &'a V, graph: &'a DirectedGraph<V>) -> HashMap<&'a V, u32>
where
    V: core::clone::Clone + std::cmp::Eq + std::hash::Hash,
{
    let mut distances = HashMap::new();
    let mut queue = VecDeque::new();
    queue.push_back((start, 0u32));

    while let Some((current, dist)) = queue.pop_front() {
        if let Some(vertices) = graph.get(current) {
            for v in vertices {
                let new_dist = dist + 1;
                distances
                    .entry(v)
                    .and_modify(|old_dist| assign_if_greater(old_dist, new_dist))
                    .or_insert(new_dist);

                queue.push_back((v, new_dist));
            }
        }
    }

    distances
}

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
*/
