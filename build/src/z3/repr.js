import assert from 'assert';
import { Z3_decl_kind } from './z3.js';
function is_array_range(z3, expr) {
    const { isBitVecVal, isApp, isAppOf, } = z3;
    if (!isApp(expr))
        return false;
    if (!isAppOf(expr, Z3_decl_kind.Z3_OP_CONCAT))
        return false;
    const args = expr.children();
    for (let i = 0; i < args.length; i++) {
        if (!isAppOf(args[i], Z3_decl_kind.Z3_OP_SELECT))
            return false;
        if (!args[i].arg(0).eq(args[0].arg(0)))
            return false;
        if (!isBitVecVal(args[i].arg(1)))
            return false; // Not necessarily required but makes it easier
        if (i > 0 &&
            args[i].arg(1).value() != args[i - 1].arg(1).value() + 1n)
            return false;
    }
    return true;
}
const OPERATIONS = new Map([
    [Z3_decl_kind.Z3_OP_LT, '<'],
    [Z3_decl_kind.Z3_OP_SLT, '<'],
    [Z3_decl_kind.Z3_OP_GT, '>'],
    [Z3_decl_kind.Z3_OP_SGT, '>'],
    [Z3_decl_kind.Z3_OP_LE, '<='],
    [Z3_decl_kind.Z3_OP_SLEQ, '<='],
    [Z3_decl_kind.Z3_OP_GE, '>='],
    [Z3_decl_kind.Z3_OP_SGEQ, '>='],
    [Z3_decl_kind.Z3_OP_EQ, '=='],
    [Z3_decl_kind.Z3_OP_DISTINCT, '!='],
    [Z3_decl_kind.Z3_OP_ADD, '+'],
    [Z3_decl_kind.Z3_OP_BADD, '+'],
    [Z3_decl_kind.Z3_OP_SUB, '-'],
    [Z3_decl_kind.Z3_OP_BSUB, '-'],
    [Z3_decl_kind.Z3_OP_MUL, '*'],
    [Z3_decl_kind.Z3_OP_BMUL, '*'],
    [Z3_decl_kind.Z3_OP_DIV, '/'],
    [Z3_decl_kind.Z3_OP_BSDIV, '/'],
    [Z3_decl_kind.Z3_OP_BUDIV, '/'],
    [Z3_decl_kind.Z3_OP_MOD, '%'],
    [Z3_decl_kind.Z3_OP_IMPLIES, '->'],
    [Z3_decl_kind.Z3_OP_IFF, '<=>'],
    [Z3_decl_kind.Z3_OP_AND, '&&'],
    [Z3_decl_kind.Z3_OP_OR, '||'],
    [Z3_decl_kind.Z3_OP_BAND, '&'],
    [Z3_decl_kind.Z3_OP_BOR, '|'],
    [Z3_decl_kind.Z3_OP_BXOR, '^'],
]);
const OPNAME_REWRITE = new Map([
    ['bvule', 'unsigned_le'],
    ['bvult', 'unsigned_lt'],
    ['bvuge', 'unsigned_ge'],
    ['bvugt', 'unsigned_gt'],
    ['not', '!'],
    ['bvnot', '~'],
    ['neg', '-'],
    ['bvneg', '-'],
]);
const INDENT = '  ';
function repr_of_quantifier(expr, var_stack) {
    let op_name;
    if (expr.is_forall()) {
        op_name = 'ForAll';
    }
    else if (expr.is_exists()) {
        op_name = 'Exists';
    }
    else {
        assert(expr.is_lambda());
        op_name = 'Lambda';
    }
    const new_vars = [];
    for (let i = 0; i < expr.num_vars(); i++) {
        new_vars.push(expr.var_name(i));
    }
    const var_str = new_vars.join(', ');
    const body = repr_of_expr(expr.body(), var_stack.concat(new_vars)).replace(/\n/g, `\n${INDENT}`);
    return `${op_name}(\n${INDENT}[${var_str}],\n${INDENT}${body}\n)`;
}
function __indent_str(r, amt = 1) {
    const indent_size = INDENT.repeat(amt);
    const replaced_r = r.replace(/\n/g, `\n${indent_size}`);
    return `${indent_size}${replaced_r}`;
}
function __add_next_term(op, curr, next_term) {
    if (curr.length == 0) {
        return next_term;
    }
    const last_line = curr.split('\n').pop();
    const first_line = next_term.split('\n')[0];
    if (last_line.length + first_line.length > 80) {
        const new_next_term = next_term.replace(/\n/g, `\n${INDENT}`);
        return `${curr} ${op}\n${INDENT}${new_next_term}`;
    }
    else {
        return `${curr} ${op} ${next_term}`;
    }
}
function __parenthesize(s) {
    if (s.indexOf('\n') !== -1) {
        return `(\n${__indent_str(s, 1)}\n)`;
    }
    else {
        return `(${s})`;
    }
}
export function repr_of_expr(expr, var_stack = [], indents = 0) {
    if (expr === undefined) {
        return 'undefined';
    }
    if (typeof expr === 'string') {
        return expr;
    }
    if (typeof (expr) === 'number' || typeof expr === 'bigint') {
        return expr.toString();
    }
    const z3 = expr.ctx;
    const { isBitVecVal, isApp, isFuncDecl, isSort, isVar, getVarIndex, isIntVal, isQuantifier, BitVec, } = z3;
    if (indents > 0) {
        return `\n${__indent_str(repr_of_expr(expr, var_stack), indents)}\n`;
    }
    if (isFuncDecl(expr)) {
        const f = expr;
        return f.name();
    }
    else if (isSort(expr)) {
        const s = expr;
        return s.toString();
    }
    else if (isQuantifier(expr)) {
        const q = expr;
        return repr_of_quantifier(q, var_stack);
    }
    else if (isVar(expr)) {
        const idx = getVarIndex(expr);
        if (idx >= var_stack.length) {
            return `Var(${idx})`;
        }
        return var_stack[var_stack.length - (idx + 1)];
    }
    else if (isIntVal(expr) || isBitVecVal(expr)) {
        let v;
        if (isIntVal(expr)) {
            v = expr.value().toString();
        }
        else {
            const x = expr;
            v = (x.size() > 8) ? x.asSignedValue().toString() : x.value().toString();
            if (x.asSignedValue() > 1024n && x.asSignedValue() < -1024n) {
                v = x.value().toString(16);
            }
        }
        if (isIntVal(expr) || expr.size() == 256) {
            return v;
        }
        return `bv${expr.size()}(${v})`;
    }
    expr = expr;
    if (is_array_range(z3, expr)) {
        const arr = repr_of_expr(expr.arg(0).arg(0), var_stack);
        const lo = repr_of_expr(expr.arg(0).arg(1), var_stack);
        const idxSort = expr.arg(0).arg(1).sort;
        const lastIndex = expr.arg(expr.numArgs() - 1).arg(1);
        const hi = repr_of_expr(BitVec.val(lastIndex.value() + 1n, idxSort.size()), var_stack);
        return `${arr}[${lo}:${hi}]`;
    }
    const arg_reprs = expr.children().map((x) => repr_of_expr(x, var_stack));
    const k = expr.decl().kind();
    if (k == Z3_decl_kind.Z3_OP_BNEG) {
        return '-' + __parenthesize(arg_reprs[0]);
    }
    else if (OPERATIONS.has(k)) {
        const op = OPERATIONS.get(k);
        for (let i = 0; i < arg_reprs.length; i++) {
            const sub_expr = expr.arg(i);
            const r = arg_reprs[i];
            if (isApp(sub_expr) && OPERATIONS.has(sub_expr.decl().kind())) {
                arg_reprs[i] = __parenthesize(r);
            }
        }
        return arg_reprs.reduce((curr, next) => __add_next_term(op, curr, next), '');
    }
    else if (k == Z3_decl_kind.Z3_OP_SELECT) {
        assert(arg_reprs.length == 2);
        const arr = arg_reprs[0];
        const index = arg_reprs[1];
        if (index.length > 40) {
            return `${arr}[\n${__indent_str(index)}\n]`;
        }
        return `${arr}[${index}]`;
    }
    const param_and_args = expr.params().map((x) => repr_of_expr(x, var_stack)).concat(arg_reprs);
    let content = param_and_args.join(', ');
    if (content.length > 65) {
        content = `\n${__indent_str(param_and_args.join(',\n'), 1)}\n`;
    }
    if (k == Z3_decl_kind.Z3_OP_CONST_ARRAY) {
        const d = expr.domain();
        content = `${d.name()} -> ${repr_of_expr(expr.arg(0), var_stack)}`;
    }
    if (content.length > 0) {
        content = `(${content})`;
    }
    let opname = expr.decl().name();
    if (OPNAME_REWRITE.has(opname)) {
        opname = OPNAME_REWRITE.get(opname);
    }
    return `${opname}${content}`;
}
