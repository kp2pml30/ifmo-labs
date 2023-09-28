const std = @import("std");

const lexer = @import("ts/lexer.zig");
const parser = @import("ts/parser.zig");

pub const Inst = struct { ptr: *anyopaque };

const dbg =
    \\function main(): number {
    \\  let x = 1;
    \\  let y = f(10);
    \\  if (x == y) {
    \\    x = y;
    \\  } else {
    \\    x = 11;
    \\  }
    \\  return x;
    \\}
;

const GlobalAllocator = std.heap.GeneralPurposeAllocator(.{});

pub fn main() !void {
    var globalAllocator: GlobalAllocator = .{};
    defer std.debug.assert(globalAllocator.deinit() == .ok);
    var lex = lexer.Lexer.init(globalAllocator.allocator(), dbg);
    defer lex.deinit();

    var par = parser.Parser.init(&lex, globalAllocator.allocator());
    defer par.deinit();

    const res = par.parse();

    std.debug.print("token {}\n", .{res.body});
}
