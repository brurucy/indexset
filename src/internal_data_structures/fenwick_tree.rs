fn least_significant_bit(idx: isize) -> isize {
    return idx & -idx;
}

fn most_significant_bit(idx: isize) -> isize {
    let mut result = idx;

    result |= result >> 1;
    result |= result >> 2;
    result |= result >> 4;
    result |= result >> 8;
    result |= result >> 16;
    result |= result >> 32;

    return result - (result >> 1);
}

#[derive(Debug, Clone, PartialEq)]
pub struct FenwickTree {
    inner: Vec<usize>,
}

impl FenwickTree {
    pub fn new<T>(container: impl IntoIterator<Item = T>, f: impl Fn(&T) -> usize) -> Self {
        let mut inner = vec![];
        container.into_iter().enumerate().for_each(|(idx, value)| {
            let length = f(&value);
            inner.push(length);
            if idx > 0 {
                inner[idx] += inner[idx - 1];
            }
        });

        let inner_two = inner.clone();
        inner.iter_mut().enumerate().rev().for_each(|(idx, item)| {
            let lower_bound = (idx as isize & (idx as isize + 1)) - 1;
            if lower_bound >= 0 {
                *item -= inner_two[lower_bound as usize];
            }
        });

        return FenwickTree { inner };
    }

    pub fn prefix_sum(&self, idx: usize) -> usize {
        let mut sum = 0;
        let mut current_idx = idx;

        if idx > self.inner.len() {
            return sum;
        }

        while current_idx > 0 {
            sum += self.inner[current_idx - 1];
            current_idx &= current_idx - 1
        }

        return sum;
    }
    pub fn increase_length(&mut self, idx: usize) {
        let mut current_idx = idx;
        while current_idx < self.inner.len() {
            self.inner[current_idx] += 1;
            current_idx |= current_idx + 1
        }
    }
    pub fn decrease_length(&mut self, idx: usize) {
        let mut current_idx = idx;
        while current_idx < self.inner.len() {
            self.inner[current_idx] -= 1;
            current_idx |= current_idx + 1
        }
    }
    pub fn index_of(&self, prefix_sum: usize) -> usize {
        let length = self.inner.len() as isize;
        let mut prefix_sum = prefix_sum;
        let mut idx = 0 as isize;
        let mut x = most_significant_bit(length) * 2;
        while x > 0 {
            let lsb = least_significant_bit(x);
            if x <= length && self.inner[(x - 1) as usize] < prefix_sum {
                idx = x;
                prefix_sum -= self.inner[(x - 1) as usize];
                x += lsb / 2;
            } else {
                if lsb % 2 > 0 {
                    break;
                }
                x += lsb / 2 - lsb;
            }
        }
        return idx as usize;
    }
}

#[cfg(test)]
mod tests {
    use super::FenwickTree;

    #[test]
    fn test_new() {
        let lengths: [usize; 5] = [1, 6, 3, 9, 2];
        let expected_index: Vec<usize> = vec![1, 7, 3, 19, 2];
        let actual_index = FenwickTree::new(lengths, |item| *item);
        assert_eq!(expected_index, actual_index.inner)
    }

    #[test]
    fn test_prefix_sum() {
        let lengths = [1, 6, 3, 9, 2];
        let fenwick_array = FenwickTree::new(lengths, |item| *item);

        let cases: Vec<(usize, usize)> =
            vec![(0, 0), (1, 1), (2, 7), (3, 10), (4, 19), (5, 21), (6, 0)];
        // The prefix sum up until the zeroth element is 0, since there is nothing before it
        // The prefix sum up until an index larger than the length is undefined, since every element after the length - 1
        // is undefined
        cases
            .into_iter()
            .for_each(|(idx, expected_sum)| assert_eq!(fenwick_array.prefix_sum(idx), expected_sum))
    }

    #[test]
    fn test_increase_length() {
        let lengths = [1, 6, 3, 9, 2];
        let mut fenwick_array = FenwickTree::new(lengths, |item| *item);

        let cases: Vec<(usize, usize)> = vec![(0, 2), (1, 8), (2, 3), (3, 20), (4, 2)];

        fenwick_array.increase_length(0);

        cases
            .into_iter()
            .for_each(|(idx, expected_value)| assert_eq!(fenwick_array.inner[idx], expected_value))
    }

    #[test]
    fn test_index_of() {
        let lengths: Vec<usize> = vec![1, 6, 3, 9, 2];
        let fenwick_array = FenwickTree::new(lengths, |item| *item);

        let cases: Vec<(usize, usize)> = vec![(0, 0), (6, 1), (9, 2), (18, 3), (20, 4)];

        cases
            .into_iter()
            .for_each(|(prefix_sum, idx)| assert_eq!(fenwick_array.index_of(prefix_sum), idx))
    }
}
