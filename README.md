# Achilles (working title)

An example is the best way to introduce a language, so here's an example:

```
function fib(n: natural) {
  if (n == 0) return 0;
  if (n == 1) return 1;
  return fib(n - 1) + fib(n - 2);
}

function fib-tail(n: natural, a: natural, b: natural) {
  if (n == 0) return a;
  if (n == 1) return b;
  return fib-tail(n - 1, b, a + b);
}

function fib-fast(n) {
  return fib-tail(n, 0, 1);
}

theorem |fib-fast == fib|(x: natural) {
  return fib-fast(x) == fib(x);
}
```

Achilles is a little language that uses the [ACL2 theorem prover](https://www.cs.utexas.edu/~moore/acl2/) to execute functions and prove theorems. Its familiar C-like syntax enforces the constraints of ACL2 automatically.

Compared to writing raw ACL2, Achilles presents:

- A C-like syntax that's more familiar to most programmers
- A straightforward way to print debugging information
- The ability to define aliases without deep nesting
- Parameter types for functions and theorems that set up total functions and sane theorems without effort
- Syntactic sugar for common list operations like `map`, `flatMap`, `reduce`, `filter`, and `zipWith`

## Appendix A: ACL2 output for above example

```lisp
(defun fib (n)
  (if (not (and (natp n)))
      nil
      (if (= n 0)
          0
          (if (= n 1)
              1
              (+ (fib (- n 1)) (fib (- n 2)))))))

(defun fib-tail (n a b)
  (if (not (and (natp n) (natp a) (natp b)))
      nil
      (if (= n 0)
          a
          (if (= n 1)
              b
              (fib-tail (- n 1) b (+ a b))))))

(defun fib-fast (n)
  (if (not (and (natp n))
      nil
      (fib-tail n 0 1))))

(defthm |fib-fast == fib|
  (implies (and (natp x))
    (= (fib-fast x) (fib x))))

```

This is not an officially supported Google product
