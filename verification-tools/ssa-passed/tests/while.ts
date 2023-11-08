function main(): number {
    let y = 11

    while (g()) {
        y = y
        f(y)
    }
    return y
}
