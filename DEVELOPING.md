# Developing

## Coverage

Use the Coverage Gutters extension. Enable it with the appropriate command and
start the watch command. Run this:

```
deno test --allow-all --coverage=cov_profile -- -u && deno coverage cov_profile --lcov --output=lcov.info
```
