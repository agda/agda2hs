# Developer Documentation

## Running the Test Suite

The test suite uses `tasty-golden` for golden value testing. Tests are organized into two categories:

- **Succeed tests** (`test/Succeed/`): Agda files that should compile successfully with agda2hs. The generated `.hs` files are the golden values.
- **Fail tests** (`test/Fail/`): Agda files that should fail to compile. The error messages (in `.err` files) are the golden values.

### Running All Tests

```bash
# Run all tests (includes whitespace check and container tests)
make test

# Or run just the agda2hs tests
cabal test agda2hs-test
```

### Running Specific Test Categories

```bash
# Run only successful tests
make succeed

# Run only failing tests
make fail

# Or using cabal directly with pattern matching
cabal test agda2hs-test --test-options='-p Succeed'
cabal test agda2hs-test --test-options='-p Fail'
```

### Running Individual Tests

```bash
# Run a specific test by name
cabal test agda2hs-test --test-options='-p /Fixities/'

# Run tests matching a pattern
cabal test agda2hs-test --test-options='-p /Issue/'
```

## Updating Golden Values

When you make changes that intentionally affect the test output, you need to update the golden values:

```bash
# Update all golden values
make golden

# Update only successful test golden values
make golden-succeed

# Update only failing test golden values
make golden-fail

# Or using cabal directly
cabal test agda2hs-test --test-options='--accept'
```

After updating golden values, review the changes with `git diff` to ensure they are correct before committing.

## Adding New Tests

### Adding a Succeed Test

1. Create a new `.agda` file in `test/Succeed/`
2. Run `make golden-succeed` to generate the golden `.hs` file
3. Verify the generated Haskell code is correct
4. Commit both the `.agda` and `.hs` files

### Adding a Fail Test

1. Create a new `.agda` file in `test/Fail/`
2. Run `make golden-fail` to generate the golden `.err` file
3. Verify the error message is correct
4. Commit both the `.agda` and `.err` files

## Test Ordering

Tests are ordered by:
1. Modification date of the `.agda` file (newest first)
2. Modification date of the golden value file (newest first)
3. Alphabetically

This ordering ensures that recently modified tests appear first in the output, making it easier to focus on tests you're actively working on.
