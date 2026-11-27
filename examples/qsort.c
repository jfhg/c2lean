//@ requires c:a < m₀.next && c:b < m₀.next;
//@ ensures  cur (c:a) == old (c:b) && cur (c:b) == old (c:a);
void swap(int* a, int* b) {
    int temp = *a;
    *a = *b;
    *b = temp;
}

int partition(int arr[], int low, int high) {

    // Initialize pivot to be the first element
    int p = arr[low];
    int i = low;
    int j = high;

    while (i < j) {

        // Find the first element greater than
        // the pivot (from starting)
        while (arr[i] <= p && i <= high - 1) {
            i++;
        }

        // Find the first element smaller than
        // the pivot (from last)
        while (arr[j] > p && j >= low + 1) {
            j--;
        }
        if (i < j) {
            swap(&arr[i], &arr[j]);
        }
    }
    swap(&arr[low], &arr[j]);
    return j;
}

void quickSort(int arr[], int low, int high) {
    if (low < high) {

        // call partition function to find Partition Index
        int pi = partition(arr, low, high);

        // Recursively call quickSort() for left and right
        // half based on Partition Index
        quickSort(arr, low, pi - 1);
        quickSort(arr, pi + 1, high);
    }
}

//@ requires validAt c:a c:n && c:n <= 8 && 1024 <= m₀.next && SmallAt old c:a c:n;
//@ ensures  SortedAt cur c:a c:n && PermAt cur old c:a c:n;
void sort(int *a, int n) {
    if (n > 0) quickSort(a, 0, n - 1);
}
