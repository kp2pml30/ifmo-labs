const lexer = @import("./lexer.zig");
const std = @import("std");

pub const File = struct {
    name: []const u8,
    args: [][]const u8,
    body: *Statement,
};

pub const Expr = union(enum) {
    BiOp: struct {
        op: lexer.Operator,
        left: *Expr,
        right: *Expr,
    },
    Ident: []const u8,
    Literal: []const u8,
};

pub const Statement = union(enum) {
    Block: []*Statement,
    If: struct {
        cond: *Expr,
        ifTrue: *Statement,
        ifFalse: ?*Statement,
    },
    Break,
    Continue,
    Return: ?*Statement,
    Expr: *Expr,
};

pub const Parser = struct {
    lex: *lexer.Lexer,
    allocator: std.heap.ArenaAllocator,

    pub fn init(lex: *lexer.Lexer, all: std.mem.Allocator) Parser {
        return .{
            .lex = lex,
            .allocator = std.heap.ArenaAllocator.init(all),
        };
    }

    pub fn deinit(self: *Parser) void {
        self.allocator.deinit();
    }

    fn alloc(self: *Parser, e: anytype) *@TypeOf(e) {
        var r = self.allocator.allocator().create(@TypeOf(e)) catch unreachable;
        r.* = e;
        return r;
    }

    fn expect(self: *Parser, t: lexer.Token) void {
        const nxt = self.lex.next().?;
        if (!std.mem.eql(u8, @tagName(nxt), @tagName(t))) {
            unreachable;
        }
        // todo...
    }

    fn getIdent(self: *Parser) []const u8 {
        switch (self.lex.next().?) {
            lexer.Token.ident => |i| return i,
            else => unreachable,
        }
    }

    fn parseStatement(self: *Parser) *Statement {
        switch (self.lex.peek().?) {
            lexer.Token.LCPar => return self.parseBlock(),
            lexer.Token.Keyword => |k| {
                switch (k) {}
            },
            else => {
                const e = self.parseExpr();
                self.expect(lexer.Token.SEMI);
                return self.alloc(Statement{ .Expr = e });
            },
        }
    }

    fn parseBlock(self: *Parser) *Statement {
        self.expect(lexer.Token.LCPar);
        var sts = std.ArrayList(*Statement).init(self.allocator.allocator());
        while (self.lex.peek().? != lexer.Token.RCPar) {
            (sts.addOne() catch unreachable).* = self.parseStatement();
        }
        self.expect(lexer.Token.RCPar);
        return self.alloc(Statement{ .Block = sts.toOwnedSlice() catch unreachable });
    }

    fn skipType(self: *Parser) void {
        self.expect(lexer.Token.COLON);
        _ = self.getIdent();
    }

    pub fn parse(self: *Parser) File {
        self.expect(lexer.Token{ .kw = lexer.Keyword.FUNCTION });
        const name = self.getIdent();
        self.expect(lexer.Token.LPar);
        self.expect(lexer.Token.RPar);
        self.skipType();
        const st = self.parseBlock();
        return .{
            .name = name,
            .args = &.{},
            .body = st,
        };
    }

    fn parseExpr(self: *Parser) *Expr {
        return self.parseAtom();
    }

    fn parseAtom(self: *Parser) *Expr {
        return switch (self.lex.next().?) {
            lexer.Token.LPar => blk: {
                var r = self.parseExpr();
                self.expect(lexer.Token.RPar);
                break :blk r;
            },
            lexer.Token.ident => |t| self.alloc(Expr{ .Ident = t }),
            lexer.Token.Literal => |t| self.alloc(Expr{ .Literal = t }),
            else => |t| err(t),
        };
    }

    fn err(x: anytype) noreturn {
        std.debug.print("{}", .{x});
        unreachable;
    }
};
