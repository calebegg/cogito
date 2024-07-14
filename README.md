# [Cogito](https://cogitolang.org)

## Examples

```c
function factorial(n: natural) {
  print("Factorializing ~x0", n);
  if (n == 0) {
    return 1;
  }
  return n * factorial(n - 1);
}

function add-to-end(xs: list, x: any) {
  if (empty(xs)) {
    return [x];
  } else {
    return concat([first(xs)], add-to-end(rest(xs), x));
  }
}
function rev(xs: list) {
  return reduce(xs as acc, x from []) {
    return add-to-end(acc, x)
  };
}
theorem |rev twice returns original list|(xs: list) {
  return rev(rev(xs)) == xs
}

// TODO: add measure
function merge(xs: list, ys: list) {
  if (empty(xs)) return ys;
  if (empty(ys)) return xs;
  if (first(xs) < first(ys)) {
    return [first(xs), ...merge(rest(xs), ys)];
  }
  return [first(ys), ...merge(xs, rest(ys))];
}

function foo() {
  x = 3;
  if (x < 5) {
    x = 4
  } else {
    x = 2
  }
  x = x + 3
  return x - 1
}

function sum(xs: list<number>) {
  return reduce(xs as acc, x from 0) {
    return acc + x;
  }
}
```
