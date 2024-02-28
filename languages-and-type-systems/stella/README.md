# stella

## How to build and run
1. install haskell tool stack (ghcup is recommended)
2.
    ```bash
    cd "$PROJECT"
    stack build
    ./test/run-golden.rb --runner ./test/stack-driver.sh
    ```
