const ApiCall = (a: any, b: any) => {}
const KeyClass = (a: any, b: any) => {}

@KeyClass
abstract class A {
    abstract foo(): number
}

abstract class B extends A {
    abstract override foo(): any
}

class C extends A {
    fld: number
    foo(): number { return 0 }
    @ApiCall
    bar(a: number): number {
        return a * a + (a == 0 ? 0 : this.bar(a / 2))
    }
}
