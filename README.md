# Achilles (working title)

```
function is-palindrome(l: list) {
  reversed = reverse(l);
  print("Original list: ~x0", l);
  print("Reversed list: ~x0", reversed);
  return l == reversed;
}

theorem |is-palindrome is equivalent on a reversal|(l: list) {
  return is-palindrome(reverse(l)) == is-palindrome(l);
}
theorem |is-palindrome works on even palindromes|(l: list) {
  return is-palindrome([...l, ...reverse(l)]);
}
theorem |is-palindrome works on odd palindromes|(l: list, x: any) {
  return is-palindrome([...l, x, ...reverse(l)]);
}
```

Achilles is a simple programming language that uses the [ACL2 theorem prover](https://www.cs.utexas.edu/~moore/acl2/) to execute functions and prove theorems. Its familiar C-like syntax enforces the constraints of ACL2 automatically.

Compared to writing raw ACL2, Achilles presents:

- A C-like syntax that's more familiar to most programmers
- A straightforward way to print debugging information
- The ability to easily define aliases without deep nesting
- Parameter types for functions and theorems that set up total functions and sane theorems without extra effort
- Syntactic sugar for common list operations like `map`, `flatMap`, `reduce`, `filter`, and `zipWith`

The intent of Achilles is to be a gentle way to access ACL2's power, specifically through the lens of a teaching language for students unfamiliar with functional programming languages. Achilles supplies **guard rails** to make sure that the user is writing code that is more likely to succeed in proof attempts without as much cognitive overhead.

## Examples



## Appendix: ACL2 code output for above example

```lisp
(defun is-palindrome (l)
  (declare (xargs :guard (and (true-listp l))))
  (if (not (and (true-listp l)))
      0
      (let ((reversed (reverse l)))
           (prog2$ (cw "Original list: ~x0~%" l)
                   (prog2$ (cw "Reversed list: ~x0~%" reversed)
                           (equal l reversed))))))

(defthm |is-palindrome is equivalent on a reversal|
  (implies (true-listp l)
           (equal (is-palindrome (reverse l))
                  (is-palindrome l))))
(defthm |is-palindrome works on even palindromes|
  (implies (true-listp l)
           (is-palindrome (append l (reverse l)))))
(defthm |is-palindrome works on odd palindromes|
  (implies (true-listp l)
           (is-palindrome (append l (list x) (reverse l)))))
```

This is not an officially supported Google product
