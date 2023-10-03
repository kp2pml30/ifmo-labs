function main(): number {
    let y = 11

    while (g()) {
        y = y + 10
        if (f(y)) {
            break
            y = y + 1
        }
    }
    return y
}
