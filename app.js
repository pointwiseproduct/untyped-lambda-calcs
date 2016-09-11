var Token = (function () {
    function Token(str, column, row) {
        this.str = str;
        this.column = column;
        this.row = row;
    }
    return Token;
})();
function copy(object) {
    var objectCopy = {};
    for (var key in object) {
        objectCopy[key] = object[key];
    }
    return objectCopy;
}
function copyArray(object) {
    return object.concat();
}
var Identifier = (function () {
    function Identifier(t) {
        this.t = t;
    }
    Identifier.prototype.kind = function () {
        return "Identifier";
    };
    Identifier.prototype.some = function (other) {
        return other.kind() == this.kind() && this.t.str == other.t.str;
    };
    Identifier.prototype.recursiveReplace = function (p) {
        if (this.t.str == p[0]) {
            return p[1].copy();
        }
        else {
            return null;
        }
    };
    Identifier.prototype.replace = function (p) {
        if (this.t.str == p[0]) {
            return p[1].copy();
        }
        else {
            return null;
        }
    };
    Identifier.prototype.eval = function (step, lambdaCalcs) {
        return [null, this.t.str];
    };
    Identifier.prototype.toString = function (inBracket) {
        return this.t.str;
    };
    Identifier.prototype.copy = function () {
        return copy(this);
    };
    Identifier.prototype.constraintCopy = function (partial) {
        if (partial == this) {
            var a = copy(this);
            return [a, a];
        }
        else {
            return [copy(this), copy(this)];
        }
    };
    Identifier.prototype.reduce = function (p) {
        if (this.some(p[1])) {
            return new Identifier(new Token(p[0], 0, 0));
        }
        else {
            return this.copy();
        }
    };
    Identifier.prototype.size = function () {
        return 1;
    };
    return Identifier;
})();
var Sequence = (function () {
    function Sequence() {
        this.seq = new Array();
    }
    Sequence.prototype.kind = function () {
        return "Sequence";
    };
    Sequence.prototype.some = function (other) {
        if (other.kind() != this.kind() || this.seq.length != other.seq.length) {
            return false;
        }
        var x = true;
        for (var i = 0; i < this.seq.length; ++i) {
            x = x && this.seq[i].some(other.seq[i]);
        }
        return x;
    };
    Sequence.prototype.recursiveReplace = function (p) {
        var t = this.copy();
        var mod = false;
        for (var i = 0; i < t.seq.length; ++i) {
            var r = t.seq[i].recursiveReplace(p);
            if (r != null) {
                t.seq[i] = r;
                mod = true;
            }
        }
        if (mod) {
            return t;
        }
        else {
            return null;
        }
    };
    Sequence.prototype.replace = function (p) {
        var t = this.copy();
        var mod = false;
        for (var i = 0; i < t.seq.length; ++i) {
            var r = t.seq[i].replace(p);
            if (r != null) {
                t.seq[i] = r;
                mod = true;
            }
        }
        if (mod) {
            return t;
        }
        else {
            return null;
        }
    };
    Sequence.prototype.eval = function (step, lambdaCalcs, normal) {
        var key = "(";
        var mod = false;
        var s = new Sequence();
        var c = [null, null];
        for (var i = 0; i < this.seq.length; ++i) {
            var c = this.seq[i].eval(step, lambdaCalcs, normal);
            var d = c[0];
            key += c[1];
            if (i < this.seq.length - 1) {
                key += " ";
            }
            while (c[0] != null) {
                mod = true;
                d = c[0];
                c = d.eval(step, lambdaCalcs, normal);
            }
            s.seq.push(d == null ? this.seq[i].copy() : d);
        }
        key += ")";
        var tmp = lambdaCalcs.exprMemo[key];
        if (tmp != null) {
            return [tmp[0], key];
        }
        while (true) {
            var pmod = false;
            if (s.seq[0].kind() == "Lambda") {
                var r;
                var l = (s.seq[0]);
                var len = Math.min(s.seq.length - 1, l.args.length);
                for (var i = 0; i < len; ++i) {
                    r = l.content.recursiveReplace([l.args[i][0], s.seq[i + 1]]);
                    if (r != null) {
                        l.content = r;
                        pmod = true;
                    }
                }
                c = l.content.eval(step, lambdaCalcs, normal);
                var u = c[0];
                if (u == null) {
                    u = l.content;
                }
                var t = new Sequence();
                t.seq.push(u);
                Array.prototype.push.apply(t.seq, s.seq.slice(len + 1, s.seq.length));
                if (t.seq.length > 1) {
                    s = t;
                    mod = true;
                    continue;
                }
                else {
                    if (len < l.args.length) {
                        l.args = l.args.slice(len, l.args.length);
                        l.content = t.seq[0];
                        l = l.normalizeNestedStructure();
                        lambdaCalcs.exprMemo[key] = [copy(l)];
                        return [l, key];
                    }
                    else {
                        c = t.seq[0].eval(step, lambdaCalcs, normal);
                        var v = c[0];
                        if (v == null) {
                            lambdaCalcs.exprMemo[key] = [copy(t.seq[0])];
                            return [t.seq[0], key];
                        }
                        else {
                            lambdaCalcs.exprMemo[key] = [copy(v)];
                            return [v, key];
                        }
                    }
                }
            }
            else {
                break;
            }
        }
        if (mod) {
            lambdaCalcs.exprMemo[key] = [s.copy()];
            return [s, key];
        }
        else {
            lambdaCalcs.exprMemo[key] = [null];
            return [null, key];
        }
    };
    Sequence.prototype.toString = function (inBracket) {
        var str = "";
        if (inBracket) {
            str += "(";
        }
        for (var i = 0; i < this.seq.length; ++i) {
            if (i > 0) {
                str += " ";
            }
            str += this.seq[i].toString(true);
        }
        if (inBracket) {
            str += ")";
        }
        return str;
    };
    Sequence.prototype.copy = function () {
        var s = new Sequence;
        for (var i = 0; i < this.seq.length; ++i) {
            s.seq.push(this.seq[i].copy());
        }
        return s;
    };
    Sequence.prototype.constraintCopy = function (partial) {
        if (partial == this) {
            var a = this.copy();
            return [a, a];
        }
        else {
            var second = null;
            var s = new Sequence;
            for (var i = 0; i < this.seq.length; ++i) {
                var b = this.seq[i].constraintCopy(partial);
                if (b[1] != null) {
                    second = b[1];
                }
                s.seq.push(b[0]);
            }
            return [s, second];
        }
    };
    Sequence.prototype.reduce = function (p) {
        if (p[1].some(this)) {
            return new Identifier(new Token(p[0], 0, 0));
        }
        else {
            var second = null;
            var s = new Sequence;
            for (var i = 0; i < this.seq.length; ++i) {
                s.seq.push(this.seq[i].reduce(p));
            }
            return s;
        }
    };
    Sequence.prototype.size = function () {
        var ret = 0;
        for (var i = 0; i < this.seq.length; ++i) {
            ret += this.seq[i].size();
        }
        return ret;
    };
    return Sequence;
})();
var Lambda = (function () {
    function Lambda() {
        this.args = new Array();
    }
    Lambda.prototype.kind = function () {
        return "Lambda";
    };
    Lambda.prototype.some = function (other) {
        if (other.kind() != this.kind()) {
            return false;
        }
        var a = other;
        if (a.args.length != this.args.length) {
            return false;
        }
        var x = true;
        for (var i = 0; i < this.args.length; ++i) {
            x = x && this.args[i][0] == a.args[i][0];
        }
        return x && this.content.some(a.content);
    };
    Lambda.prototype.recursiveReplace = function (p) {
        for (var i = 0; i < this.args.length; ++i) {
            if (this.args[i][0] == p[0]) {
                return null;
            }
        }
        var r = this.content.recursiveReplace(p);
        if (r != null) {
            var s = new Lambda();
            for (var i = 0; i < this.args.length; ++i) {
                s.args.push([this.args[i][0], null]);
            }
            s.content = r;
            return s;
        }
        else {
            return null;
        }
    };
    Lambda.prototype.replace = function (p) {
        for (var i = 0; i < this.args.length; ++i) {
            if (this.args[i][0] == p[0]) {
                return null;
            }
        }
        var r = this.content.replace(p);
        if (r != null) {
            var s = new Lambda();
            for (var i = 0; i < this.args.length; ++i) {
                s.args.push([this.args[i][0], null]);
            }
            s.content = r;
            return s;
        }
        else {
            return null;
        }
    };
    Lambda.prototype.eval = function (step, lambdaCalcs, normal) {
        var key = "(λ";
        for (var i = 0; i < this.args.length; ++i) {
            if (i > 0) {
                key += " ";
            }
            key += this.args[i][0];
        }
        key += ". ";
        var l = new Lambda();
        l.args = copyArray(this.args);
        var c = this.content.eval(step, lambdaCalcs, normal);
        key += c[1] + ")";
        var tmp = lambdaCalcs.exprMemo[key];
        if (tmp != null) {
            return [tmp[0], key];
        }
        var a = c[0];
        if (a == null) {
            lambdaCalcs.exprMemo[key] = [null];
            return [null, key];
        }
        c = a.eval(false, lambdaCalcs, normal);
        while (c[0]) {
            a = c[0];
            c = a.eval(false, lambdaCalcs, normal);
        }
        l.content = a;
        lambdaCalcs.exprMemo[key] = [l];
        return [l, key];
    };
    Lambda.prototype.toString = function (inBracket) {
        var str = inBracket ? "(λ" : "λ";
        for (var i = 0; i < this.args.length; ++i) {
            if (i > 0) {
                str += " ";
            }
            str += this.args[i][0];
        }
        str += ". " + this.content.toString(this.content.kind() == "Lambda");
        if (inBracket) {
            str += ")";
        }
        return str;
    };
    Lambda.prototype.copy = function () {
        var l = new Lambda;
        l.args = copyArray(this.args);
        l.content = this.content.copy();
        return l;
    };
    Lambda.prototype.constraintCopy = function (partial) {
        if (partial == this) {
            var a = this.copy();
            return [a, a];
        }
        else {
            var l = new Lambda;
            l.args = copyArray(this.args);
            var b = this.content.constraintCopy(partial);
            l.content = b[0];
            return [l, b[1]];
        }
    };
    Lambda.prototype.reduce = function (p) {
        if (this.some(p[1])) {
            return new Identifier(new Token(p[0], 0, 0));
        }
        else {
            var l = new Lambda;
            l.args = copyArray(this.args);
            var b = this.content.reduce(p);
            l.content = b;
            return l;
        }
    };
    Lambda.prototype.size = function () {
        return this.content.size() + this.args.length;
    };
    Lambda.prototype.normalizeNestedStructure = function () {
        if (this.content.kind() != this.kind()) {
            return this;
        }
        var other = this.content.normalizeNestedStructure();
        for (var i = 0; i < this.args.length; ++i) {
            for (var j = 0; j < other.args.length; ++j) {
                if (this.args[i][0] == other.args[j][0]) {
                    return this;
                }
            }
        }
        Array.prototype.push.apply(this.args, other.args);
        this.content = other.content;
        return this;
    };
    return Lambda;
})();
var ParsingFailed = (function () {
    function ParsingFailed() {
    }
    return ParsingFailed;
})();
var LambdaCalcs = (function () {
    function LambdaCalcs() {
        this.tokenized = new Array();
        this.fTable = {};
        this.exprMemo = {};
        this.rewriteHistory = new Array();
    }
    LambdaCalcs.prototype.calc = function (e, limit) {
        if (limit === void 0) { limit = 100; }
        var r = this.replace(e.copy());
        for (var i = 0; i < limit; ++i) {
            var b = this.step(r.copy());
            if (r.some(b)) {
                break;
            }
            r = b;
        }
        return r;
    };
    LambdaCalcs.prototype.eval = function (e) {
        e = this.replace(e);
        var r = e.eval(false, this)[0];
        return r ? r : e;
    };
    LambdaCalcs.prototype.step = function (e) {
        var _this = this;
        var q = function (g, f) {
            var h = g.content.recursiveReplace([g.args[0][0], f.seq[1]]);
            if (h != null) {
                g.content = _this.step(h);
            }
            g.args = g.args.slice(1, g.args.length);
            var s = new Array();
            s.push(g.content);
            Array.prototype.push.apply(s, f.seq.slice(2, f.seq.length));
            return s;
        };
        var r = e;
        var p = e;
        var z = 0;
        while (true) {
            if (e.kind() == "Sequence") {
                var f = e;
                if (f.seq[0].kind() == "Sequence") {
                    z = 0;
                    p = e;
                    e = f.seq[0];
                    continue;
                }
                else if (f.seq[0].kind() == "Lambda" && f.seq.length > 1) {
                    if (f.seq[1].kind() == "Sequence") {
                        z = 1;
                        p = e;
                        e = f.seq[1];
                        continue;
                    }
                    else {
                        f.seq = q(f.seq[0], f);
                        if (f.seq.length == 1) {
                            if (r === e) {
                                r = f.seq[0].content;
                            }
                            else {
                                p.seq[z] = f.seq[0];
                            }
                        }
                        break;
                    }
                }
                else {
                    break;
                }
            }
            else {
                break;
            }
        }
        return r;
    };
    LambdaCalcs.prototype.reduce = function (a) {
        var inv = new Array();
        for (var key in this.fTable) {
            var x = this.replace(this.fTable[key]);
            while (true) {
                var y = x.eval(false, this)[0];
                if (y != null) {
                    x = y;
                }
                else {
                    break;
                }
            }
            inv.push([key, x]);
            console.log(key, x.toString(false));
        }
        var mod = false;
        do {
            mod = false;
            var s = new Array();
            for (var i = 0; i < inv.length; ++i) {
                var b = a.reduce(inv[i]);
                if (!b.some(a)) {
                    s.push([b, b.size()]);
                    console.log(b.toString(false), s[s.length - 1][1]);
                    mod = true;
                }
            }
            if (mod) {
                a = s.sort(function (n1, n2) { return n1[1] < n2[1] ? -1 : n1[1] > n2[1] ? 1 : 0; })[0][0];
            }
        } while (mod);
        return a;
    };
    LambdaCalcs.prototype.inputColumn = function (str, num) {
        this.tokenize(str, num);
        if (this.tokenized.length > 1) {
            return this.parse();
        }
        else {
            return null;
        }
    };
    LambdaCalcs.prototype.addRewriteHistory = function (t, after) {
        this.rewriteHistory.push([t[0].constraintCopy(t[1]), after.copy()]);
    };
    LambdaCalcs.prototype.replace = function (s) {
        var mod = false;
        var r = null;
        do {
            mod = false;
            for (var key in this.fTable) {
                if (r = s.recursiveReplace([key, this.fTable[key]])) {
                    s = r;
                    mod = true;
                }
            }
        } while (mod);
        return s;
    };
    LambdaCalcs.prototype.tokenize = function (str, column) {
        var s = "";
        var row = 0;
        for (var i = 0; i < str.length; ++i, ++row) {
            if (str[i] == " " || str[i] == "\r") {
                if (s.length > 0) {
                    this.tokenized.push(new Token(s, column, row));
                }
                s = "";
            }
            else if (str[i] == "λ" || str[i] == "\\") {
                if (s.length > 0) {
                    this.tokenized.push(new Token(s, column, row - s.length - 1));
                    s = "";
                }
                this.tokenized.push(new Token("λ", column, row - 1));
            }
            else if (str[i] == ".") {
                if (s.length > 0) {
                    this.tokenized.push(new Token(s, column, row - s.length - 1));
                    s = "";
                }
                this.tokenized.push(new Token(".", column, row - 1));
            }
            else if (str[i] == "(") {
                if (s.length > 0) {
                    this.tokenized.push(new Token(s, column, row - s.length - 1));
                    s = "";
                }
                this.tokenized.push(new Token("(", column, row - 1));
            }
            else if (str[i] == ")") {
                if (s.length > 0) {
                    this.tokenized.push(new Token(s, column, row - s.length - 1));
                    s = "";
                }
                this.tokenized.push(new Token(")", column, row - 1));
            }
            else if (str[i] == "=") {
                if (s.length > 0) {
                    this.tokenized.push(new Token(s, column, row - s.length - 1));
                    s = "";
                }
                this.tokenized.push(new Token("=", column, row - 1));
            }
            else {
                s += str[i];
            }
        }
        if (s.length > 0) {
            this.tokenized.push(new Token(s, column, row - s.length - 1));
        }
    };
    LambdaCalcs.prototype.parse = function () {
        return this.pExpr(0)[0];
    };
    LambdaCalcs.prototype.pExpr = function (i) {
        var s = new Sequence;
        var r;
        do {
            if (this.tokenized[i].str == "λ" || this.tokenized[i].str == "\\") {
                r = this.pLambda(i + 1);
                s.seq.push(r[0]);
            }
            else if (this.tokenized[i].str == "(") {
                ++i;
                r = this.pExpr(i);
                ++r[1];
                s.seq.push(r[0]);
            }
            else if (this.tokenized[i].str.match("[^ \rλ\\\.\(\)=]+")) {
                r = [new Identifier(this.tokenized[i]), i + 1];
                if (r[1] < this.tokenized.length && this.tokenized[r[1]].str == "=") {
                    var e = this.pExpr(r[1] + 1);
                    var f = e[0].copy();
                    this.fTable[this.tokenized[i].str] = f;
                    r = e;
                }
                s.seq.push(r[0]);
            }
            else {
                throw ParsingFailed;
            }
            i = r[1];
        } while (i < this.tokenized.length && this.tokenized[i].str != ")");
        return [s.seq.length == 1 ? s.seq[0] : s, r[1]];
    };
    LambdaCalcs.prototype.pLambda = function (i) {
        var f = new Lambda;
        --i;
        while (++i) {
            if (i >= this.tokenized.length) {
                throw ParsingFailed;
            }
            if (this.tokenized[i].str == ".") {
                ++i;
                break;
            }
            else if (this.tokenized[i].str.match("[a-zA-Z0-9]+")) {
                f.args.push([this.tokenized[i].str, null]);
            }
            else if (this.tokenized[i].str == ".") {
                break;
            }
            else {
                throw ParsingFailed;
            }
        }
        while (i < this.tokenized.length && this.tokenized[i].str != ")") {
            var r = this.pExpr(i);
            f.content = r[0];
            i = r[1];
        }
        return [f, i];
    };
    return LambdaCalcs;
})();
function calc() {
    var l = new LambdaCalcs();
    var i = 0;
    var textarea = document.getElementsByTagName('textarea')[0];
    var s = textarea.value.split("\n");
    var e;
    for (var i = 0; i < s.length; ++i) {
        l.tokenized = new Array();
        var f = l.inputColumn(s[i], i);
        if (f) {
            e = f;
        }
    }
    var r = l.eval(e);
    var t = r.toString(false);
    var u = l.reduce(r).toString(false);
    document.getElementById("result").innerText = "result: " + u;
}
function tOnKeyUp(e) {
    if (e.ctrlKey && e.keyCode == 13) {
        calc();
    }
}
window.onload = function () {
    document.getElementsByTagName('textarea')[0].onkeyup = tOnKeyUp;
};
//# sourceMappingURL=app.js.map