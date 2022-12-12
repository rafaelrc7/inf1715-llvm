global _a : int; global _c : int; global _m : int; global _seed : int;

# Random number utilitaries
func rinit(use_default : int, a : int, c : int, m : int);
func rseed(seed : int);
func random() : int;

func rarr(n : int) : array int;

# Auxiliary functions
func powi(b : int, e : int) : int;
func is_sorted(arr : array int, size : int) : int;
func swap(arr : array int, i : int, j : int);

# Quick sort functions
func partition(arr : array int, low : int, high : int);
func quicksort_imp(arr : array int, low : int, high : int);
func quicksort(arr : array int, size : int);

func main() : int {
	rinit(1, 0, 0, 0);

	local arr_size : int = 100;
	local arr : array int = rarr(arr_size);

	if (is_sorted(arr, arr_size)) {
		return -2;
	}

	quicksort(arr, arr_size);

	return ~is_sorted(arr, arr_size);
}

func is_sorted(arr : array int, size : int) : int {
	local i : int = 1;

	while (i < size) {
		if (arr[i-1] > arr[i]) {
			return 0;
		}
		i = i + 1;
	}

	return 1;
}

func quicksort(arr : array int, size : int) {
	return quicksort_imp(arr, 0, size-1);
}

func partition(arr : array int, low : int, high : int) : int {
	local pivot : int = arr[high];

	local i : int = (low - 1);

	local j : int = low;
	while (j <= high-1) {
		if (arr[j] < pivot) {
			i = i + 1;
			swap(arr, i, j);
		}
		j = j + 1;
	}
	swap(arr, i + 1, high);
	return i + 1;
}

func quicksort_imp(arr : array int, low : int, high : int) {
	if (low < high) {
		local pi : int = partition(arr, low, high);

		quicksort_imp(arr, low, pi-1);
		quicksort_imp(arr, pi+1, high);
	}
}

func swap(arr : array int, i : int, j : int) {
	local tmp : int = arr[i];
	arr[i] = arr[j];
	arr[j] = tmp;
}

func rarr(n : int) : array int {
	local arr : array int = newarray int[n];
	local i : int = 0;
	while (i < n) {
		arr[i] = random();
		i = i + 1;
	}

	return arr;
}

func rinit(use_default : int, a : int, c : int, m : int) {
	if (use_default) {
		_a = 1664525;
		_c = 1013904223;
		_m = powi(2, 30);
	} else {
		_a = a;
		_c = c;
		_m = m;
	}

	_seed = 1;
}

func rseed(seed : int) {
	_seed = seed;
}

# LCG algorithm
func random() : int {
	_seed = (_a * _seed + _m) % _m;
	return _seed;
}

func powi(b : int, e : int) : int {
	local i : int = 0;
	local r : int = 1;
	while (i < e) {
		r = r * b;
		i = i + 1;
	}

	return r;
}

