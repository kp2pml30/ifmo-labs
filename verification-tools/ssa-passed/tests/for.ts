function main(): number {
    let x = 12
    for (let i = 0; i < g(); i = i + 1) {
        x = f(x)
    }
    return x
}
