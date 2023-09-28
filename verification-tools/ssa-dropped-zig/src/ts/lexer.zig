const std = @import("std");

pub const Keyword = enum {
    IF,
    ELSE,
    WHILE,
    FUNCTION,
    LET,
    CONST,
    BREAK,
    CONTINUE,
};

pub const Operator = enum {
    PLUS,
    MINUS,
    DIV,
    MUL,
    EQ,
    SET,
};

pub const Token = union(enum) {
    ident: []const u8,
    kw: Keyword,
    LPar,
    RPar,
    LCPar,
    RCPar,
    COLON,
    SEMI,
    Op: Operator,
    Literal: []const u8,
};

fn IdentOrSpecial(comptime T: type) type {
    return struct {
        rest: []const u8,
        result: union(enum) {
            id: []const u8,
            special: T,
        },
    };
}

const scanTrieAccum = struct {
    base: []const u8,
    len: usize = 0,
};

fn scanTrieFilterAlts(comptime T: type, comptime pref: u8, comptime alts: anytype) type {
    var typeBuilder = std.builtin.Type;
    _ = typeBuilder;
    var ok: usize = 0;
    for (alts) |a| {
        if (a.str.len > 0 and a.str[0] == pref) {
            ok += 1;
        }
    }
    var resTypeInfo: [ok]std.builtin.Type.StructField = .{};
    var i: usize = 0;
    for (alts) |a| {
        if (a.str.len > 0 and a.str[0] == pref) {
            const elementType = std.builtin.Type.Struct{
                .layout = .Auto,
                .fields = &comptime [_]std.builtin.Type.StructField{
                    .{
                        .name = "str",
                        .type = @Type(.{ .Array = std.builtin.Type.Array{
                            .len = a.str.len - 1,
                            .child = u8,
                            .sentinel = null,
                        } }),
                        .default_value = null,
                        .is_comptime = false,
                        .alignment = 0,
                    },
                    .{
                        .name = "id",
                        .type = T,
                        .default_value = null,
                        .is_comptime = false,
                        .alignment = 0,
                    },
                },
                .decls = &.{},
                .is_tuple = false,
            };

            var buf: [16]u8 = .{};
            const name = std.fmt.bufPrint(&buf, "{}", .{i}) catch unreachable;
            resTypeInfo[i] = .{
                .name = name,
                .type = @Type(.{ .Struct = elementType }),
                .default_value = null,
                .is_comptime = false,
                .alignment = 0,
            };
            i += 1;
        }
    }
    var defVal: usize = 0;
    _ = defVal;
    const struc = std.builtin.Type.Struct{
        .layout = .Auto,
        .fields = &comptime resTypeInfo,
        .decls = &.{},
        .is_tuple = true,
    };
    return @Type(.{ .Struct = struc });
}

fn scanTrie(
    comptime T: type,
    comptime alts: anytype,
    str: []const u8,
    accum: scanTrieAccum,
    comptime canEnd: fn (s: []const u8) bool,
    comptime otherwise: fn (accum: scanTrieAccum) IdentOrSpecial(T),
) IdentOrSpecial(T) {
    inline for (alts) |a| {
        if (a.str.len == 0) {
            if (canEnd(str)) {
                return .{ .rest = str, .result = .{ .special = a.id } };
            }
            continue;
        }
        if (str.len != 0) {
            const first = a.str[0];
            std.debug.assert(first != 0);
            if (first == str[0]) {
                var accum1 = accum;
                accum1.len += 1;
                const newTrie = comptime blk: {
                    var tr: scanTrieFilterAlts(T, first, alts) = undefined;
                    var i: usize = 0;
                    inline for (alts) |a1| {
                        if (a1.str.len > 0 and a1.str[0] == first) {
                            tr[i] = .{
                                .str = a1.str[1..].*,
                                .id = a1.id,
                            };
                            i += 1;
                        }
                    }
                    break :blk tr;
                };
                return scanTrie(
                    T,
                    newTrie,
                    str[1..],
                    accum1,
                    canEnd,
                    otherwise,
                );
            }
        }
    }
    return otherwise(accum);
}

fn nextNotChar(s: []const u8) bool {
    if (s.len == 0) {
        return true;
    }
    return !std.ascii.isAlphanumeric(s[0]);
}

fn scanIdent(acc: scanTrieAccum) IdentOrSpecial(Keyword) {
    var i = acc.len;
    while (i < acc.base.len and std.ascii.isAlphanumeric(acc.base[i])) {
        i += 1;
    }
    return .{
        .rest = acc.base[i..],
        .result = .{
            .id = acc.base[0..i],
        },
    };
}

fn alwaysEnd(rest: []const u8) bool {
    _ = rest;
    return true;
}

fn scanNone(acc: scanTrieAccum) IdentOrSpecial(Token) {
    std.debug.assert(acc.len == 0);
    return .{
        .rest = acc.base,
        .result = .{
            .id = &.{},
        },
    };
}

pub const Lexer = struct {
    alloc: std.heap.ArenaAllocator,
    input: []const u8,
    queue: std.DoublyLinkedList(Token) = .{},
    markArr: std.ArrayList(Token),
    markDepth: usize = 0,

    pub fn init(alloc: std.mem.Allocator, input: []const u8) Lexer {
        return .{
            .alloc = std.heap.ArenaAllocator.init(alloc),
            .input = input,
            .queue = .{},
            .markArr = std.ArrayList(Token).init(alloc),
        };
    }

    pub fn deinit(self: *Lexer) void {
        self.alloc.deinit();
    }

    fn scanTryNumber(self: *Lexer) ?Token {
        var i: usize = 0;
        var iCheckBonus: usize = 0;
        if (self.input.len >= 2 and (self.input[0] == '-' or self.input[0] == '+')) {
            i += 1;
            iCheckBonus = 1;
        }
        while (i < self.input.len and std.ascii.isDigit(self.input[i])) {
            i += 1;
        }
        if (i - iCheckBonus == 0) {
            return null;
        }
        const r = self.input[0..i];
        self.input = self.input[i..];
        return .{
            .Literal = r,
        };
    }

    fn scanToken(self: *Lexer) ?Token {
        while (self.input.len > 0 and std.ascii.isWhitespace(self.input[0])) {
            self.input = self.input[1..];
        }

        if (self.input.len == 0) {
            return null;
        }

        if (self.scanTryNumber()) |t| {
            return t;
        }

        const opRes = scanTrie(Token, .{
            .{ .str = "+", .id = Token{ .Op = .PLUS } },
            .{ .str = "-", .id = Token{ .Op = .MINUS } },
            .{ .str = "/", .id = Token{ .Op = .DIV } },
            .{ .str = "*", .id = Token{ .Op = .MUL } },
            .{ .str = "(", .id = Token.LPar },
            .{ .str = ")", .id = Token.RPar },
            .{ .str = "{", .id = Token.LCPar },
            .{ .str = "}", .id = Token.RCPar },
            .{ .str = ":", .id = Token.COLON },
            .{ .str = ";", .id = Token.SEMI },
            .{ .str = "==", .id = Token{ .Op = .EQ } },
            .{ .str = "=", .id = Token{ .Op = .SET } },
        }, self.input, scanTrieAccum{ .base = self.input }, alwaysEnd, scanNone);

        self.input = opRes.rest;
        switch (opRes.result) {
            .id => {},
            .special => |s| return s,
        }

        const res = scanTrie(Keyword, .{
            .{ .str = "if", .id = .IF },
            .{ .str = "while", .id = .WHILE },
            .{ .str = "function", .id = .FUNCTION },
            .{ .str = "let", .id = .LET },
            .{ .str = "const", .id = .CONST },
            .{ .str = "break", .id = .BREAK },
            .{ .str = "continue", .id = .CONTINUE },
        }, self.input, scanTrieAccum{ .base = self.input }, nextNotChar, scanIdent);
        self.input = res.rest;
        switch (res.result) {
            .id => |x| return Token{ .ident = x },
            .special => |x| return Token{ .kw = x },
        }
    }

    pub fn unshift(self: *Lexer, tok: Token) void {
        var to = self.alloc.child_allocator.create(@TypeOf(self.queue).Node) catch unreachable;
        to.data = tok;
        self.queue.prepend(to);
    }

    pub fn peek(self: *Lexer) ?Token {
        if (self.queue.first) |n| {
            return n.data;
        }
        var n = self.next();
        if (n) |tok| {
            var node = self.alloc.child_allocator.create(@TypeOf(self.queue).Node) catch unreachable;
            node.data = tok;
            self.queue.prepend(node);
        }
        return n;
    }

    pub fn next(self: *Lexer) ?Token {
        if (self.queue.popFirst()) |r| {
            var ret = r.data;
            self.alloc.child_allocator.destroy(r);
            return ret;
        }

        const was = self.input.len;
        if (self.scanToken()) |tok| {
            if (self.input.len == was) {
                std.debug.print("Cant parse after `{s}` ; token: {}", .{ self.input, tok });
                unreachable;
            }
            if (self.markDepth > 0) {
                (self.markArr.addOne() catch {
                    unreachable;
                }).* = tok;
            }
            return tok;
        } else {
            return null;
        }
    }
};
