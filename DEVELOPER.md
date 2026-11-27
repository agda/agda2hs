# Developer Documentation

## Running the Test Suite

The test suite uses `tasty-golden` for golden value testing. Tests are organized into four categories:

- **Succeed tests** (`test/Succeed/`): Agda files that should compile successfully with agda2hs. The generated `.hs` files are the golden values.
- **Fail tests** (`test/Fail/`): Agda files that should fail to compile. The error messages (in `.err` files) are the golden values.
- **Warn tests** (`test/Warn/`): Agda files that compile successfully but produce warnings. The warnings (in `.warn` files) are the golden values. Other `.agda` files in the directory are helper modules and are not run as tests directly.
- **Custom tests** (`test/Custom/`): Tests that need a bespoke harness instead of a plain golden comparison. The current kind is **incremental tests** (`test/Custom/Incremental/`): a test compiles a module from scratch, deletes only its output, then recompiles it while its dependencies are considered up-to-date and skipped. The regenerated `.hs` file is the golden value and must still match the clean output (see Issue #486). Other `.agda` files in the directory are helper modules and are not run as tests directly.

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

# Run only warning tests
make warn

# Run only custom tests
make custom

# Or using cabal directly with pattern matching
cabal test agda2hs-test --test-options='-p Succeed.'
cabal test agda2hs-test --test-options='-p Fail.'
cabal test agda2hs-test --test-options='-p Warn.'
cabal test agda2hs-test --test-options='-p Custom.'
```

The trailing dot in these patterns selects a test group exactly, so that, for example, a `SucceedFoo` test in another group is not matched.

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

# Update only warning test golden values
make golden-warn

# Update only custom test golden values
make golden-custom

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

### Adding a Warn Test

1. Create a new `.agda` file in `test/Warn/`
2. Create an empty `.warn` file with the same name (so that the test is discovered)
3. Run `make golden-warn` to generate the golden `.warn` file
4. Verify the warning is correct
5. Commit both the `.agda` and `.warn` files

Other `.agda` files in `test/Warn/` are treated as helper modules and are not run as tests directly.

### Adding a Custom Test

Custom tests live under `test/Custom/<Kind>/`; the current kind is an incremental test. To add one:

1. Create the test module and any helper modules it imports in `test/Custom/Incremental/`
2. Run `make golden-custom` to generate the golden `.hs` file
3. Verify the generated Haskell code is correct
4. Commit all the `.agda` files and the golden `.hs` file

Only modules with a matching golden `.hs` file are run as tests; other `.agda` files are treated as dependencies.

## Test Ordering

Tests are ordered by:
1. Modification date of the `.agda` file (newest first)
2. Modification date of the golden value file (newest first)
3. Alphabetically

This ordering ensures that recently modified tests appear first in the output, making it easier to focus on tests you're actively working on.
