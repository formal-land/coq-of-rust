use std::collections::{HashMap, HashSet, VecDeque};

type DirectedGraph<V> = HashMap<V, HashSet<V>>;

#[inline]
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
