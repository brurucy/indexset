pub const INNER_SIZE: usize = 1024;
const CUTOFF: usize = INNER_SIZE / 2;

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub(crate) struct Node<T>
where
    T: PartialOrd + Clone,
{
    pub inner: Vec<T>,
    pub max: Option<T>
}

impl<T: PartialOrd + Clone> Default for Node<T> {
    fn default() -> Self {
        return Self { inner: Vec::with_capacity(INNER_SIZE), max: None };
    }
}

impl<T: Ord + Clone> Node<T> {
    pub fn new() -> Self {
        return Default::default();
    }
    pub fn get(&self, index: usize) -> Option<&T> {
        return self.inner.get(index);
    }
    pub fn split_off(&mut self, cutoff: usize) -> Self {
        // Split the vector at the cutoff point
        let latter_inner = self.inner.split_off(cutoff);

        // Update the max value in the current Node
        self.max = self.inner.last().cloned();

        // Create and return the new Node
        Self {
            inner: latter_inner,
            max: self.inner.last().cloned(),
        }
    }
    pub fn halve(&mut self) -> Self {
        return self.split_off(CUTOFF);
    }
    pub fn len(&self) -> usize {
        return self.inner.len();
    }
    #[inline]
    pub fn insert(&mut self, value: T) -> bool {
        match self.inner.binary_search(&value) {
            Ok(_) => return false, // Already present
            Err(idx) => {
                if let Some(max) = &self.max {
                    if &value > max {
                        self.max = Some(value.clone())
                    }
                } else {
                    self.max = Some(value.clone())
                }

                self.inner.insert(idx, value);
            },
        }

        return true;
    }
    pub fn remove(&mut self, value: &T) -> bool {
        match self.inner.binary_search(value) {
            Ok(idx) => {
                self.inner.remove(idx);
                if Some(value) == self.max.as_ref() {
                    self.max = self.inner.last().cloned();
                }

                true
            },
            Err(_) => false,  // Not found
        }
    }
    pub fn delete(&mut self, index: usize) -> T {
        return self.inner.remove(index);
    }
}

#[cfg(test)]
mod tests {
    use super::{Node, CUTOFF, INNER_SIZE};

    #[test]
    fn test_insert() {
        let input: Vec<isize> = vec![1, 9, 2, 7, 6, 3, 5, 4, 10, 8];

        let expected_output: Vec<isize> = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

        let actual_vertebra = input.iter().fold(Node::new(), |mut acc, curr| {
            acc.insert(curr);
            acc
        });

        let actual_output: Vec<isize> = actual_vertebra.inner.into_iter().cloned().collect();

        assert_eq!(expected_output, actual_output);
        assert_eq!(*actual_vertebra.max.unwrap(), 10);
    }

    #[test]
    fn test_remove() {
        let input: Vec<isize> = vec![1, 9, 2, 7, 6, 3, 5, 4, 10, 8];
        let mut actual_vertebra = input.iter().fold(Node::new(), |mut acc, curr| {
            acc.insert(curr.clone());
            acc
        });
        let deletions: Vec<isize> = vec![1, 2, 4, 5, 10];
        deletions.into_iter().for_each(|each| {
            actual_vertebra.remove(&each);
        });

        let expected_output: Vec<isize> = vec![3, 6, 7, 8, 9];

        let actual_output: Vec<isize> = actual_vertebra.inner.into_iter().collect();

        assert_eq!(expected_output, actual_output);
        assert_eq!(actual_vertebra.max.unwrap(), 9);
    }

    #[test]
    fn test_halve() {
        let mut input: Vec<isize> = vec![];
        for item in 0..INNER_SIZE {
            input.push(item.clone() as isize);
        }

        let mut former_vertebra = Node::new();
        input.iter().for_each(|item| {
            former_vertebra.insert(item.clone());
        });
        let latter_vertebra = former_vertebra.halve();

        let expected_former_output: Vec<isize> = input[0..CUTOFF].to_vec();
        let expected_latter_output: Vec<isize> = input[CUTOFF..].to_vec();

        let actual_former_output: Vec<isize> = former_vertebra.inner.iter().cloned().collect();
        let actual_latter_output: Vec<isize> = latter_vertebra.inner.iter().cloned().collect();

        assert_eq!(expected_former_output, actual_former_output);
        assert_eq!(expected_latter_output, actual_latter_output);
    }
}
