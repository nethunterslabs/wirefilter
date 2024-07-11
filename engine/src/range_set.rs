use std::{borrow::Borrow, cmp::Ordering, iter::FromIterator, ops::RangeInclusive};

/// RangeSet provides a set-like interface that allows to search for items while
/// being constructed from and storing inclusive ranges in a compact fashion.
pub struct RangeSet<T> {
    ranges: Vec<RangeInclusive<T>>,
}

impl<T: Ord + Copy> From<Vec<RangeInclusive<T>>> for RangeSet<T> {
    // Convert from vector and prepare for binary search.
    fn from(mut ranges: Vec<RangeInclusive<T>>) -> Self {
        ranges.sort_unstable_by_key(|range| *range.start());
        // `dedup_by` invokes callback with mutable references, which allows not only
        // to remove same consecutive items, but also to provide custom merging
        // implementation which is exactly what we want for overlapping ranges.
        ranges.dedup_by(|b, a| {
            if b.start() <= a.end() {
                if b.end() > a.end() {
                    *a = *a.start()..=*b.end();
                }
                true
            } else {
                false
            }
        });
        RangeSet { ranges }
    }
}

impl<T: Ord + Copy> FromIterator<RangeInclusive<T>> for RangeSet<T> {
    fn from_iter<I: IntoIterator<Item = RangeInclusive<T>>>(ranges: I) -> Self {
        Vec::from_iter(ranges).into()
    }
}

impl<T> RangeSet<T> {
    /// Like [`HashSet::contains`](std::collections::HashSet::contains),
    /// checks whether any compatible type is in the set.
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: ?Sized + Ord,
    {
        self.ranges
            .binary_search_by(|range| {
                if range.start().borrow() > value {
                    Ordering::Greater
                } else if range.end().borrow() >= value {
                    Ordering::Equal
                } else {
                    Ordering::Less
                }
            })
            .is_ok()
    }
}

#[derive(PartialEq, Eq)]
pub(crate) struct RangeSetWithId<T> {
    ranges: Vec<(RangeInclusive<T>, usize)>,
}

impl<T: Ord + Copy> From<Vec<(RangeInclusive<T>, usize)>> for RangeSetWithId<T> {
    fn from(mut ranges: Vec<(RangeInclusive<T>, usize)>) -> Self {
        ranges.sort_unstable_by_key(|(range, _)| *range.start());
        ranges.dedup_by(|(b, _), (a, _)| {
            if b.start() <= a.end() {
                if b.end() > a.end() {
                    *a = *a.start()..=*b.end();
                }
                true
            } else {
                false
            }
        });
        RangeSetWithId { ranges }
    }
}

impl<T: Ord + Copy> FromIterator<(RangeInclusive<T>, usize)> for RangeSetWithId<T> {
    fn from_iter<I: IntoIterator<Item = (RangeInclusive<T>, usize)>>(ranges: I) -> Self {
        Vec::from_iter(ranges).into()
    }
}

impl<T> RangeSetWithId<T> {
    pub fn is_continuous(&self) -> bool
    where
        T: PartialOrd,
    {
        if self.ranges.is_empty() {
            return true;
        }

        self.ranges.windows(2).all(|window| {
            let ((prev, _), (next, _)) = (&window[0], &window[1]);
            prev.end() >= next.start()
        })
    }

    pub fn get(&self, index: usize) -> Option<&(RangeInclusive<T>, usize)> {
        self.ranges.get(index)
    }

    pub fn get_min_start(&self) -> Option<T>
    where
        T: Ord + Copy,
    {
        self.ranges.iter().map(|(range, _)| *range.start()).min()
    }

    pub fn get_min_start_with_condition(&self, condition: impl Fn(&T) -> bool) -> Option<T>
    where
        T: Ord + Copy,
    {
        self.ranges
            .iter()
            .filter_map(|(range, _)| {
                if condition(range.start()) {
                    Some(*range.start())
                } else {
                    None
                }
            })
            .min()
    }

    pub fn get_max_end(&self) -> Option<T>
    where
        T: Ord + Copy,
    {
        self.ranges.iter().map(|(range, _)| *range.end()).max()
    }

    pub fn get_max_end_with_condition(&self, condition: impl Fn(&T) -> bool) -> Option<T>
    where
        T: Ord + Copy,
    {
        self.ranges
            .iter()
            .filter_map(|(range, _)| {
                if condition(range.end()) {
                    Some(*range.end())
                } else {
                    None
                }
            })
            .max()
    }

    pub fn len(&self) -> usize {
        self.ranges.len()
    }
}
