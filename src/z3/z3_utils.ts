import {Expr, Z3_decl_kind} from "./z3";

export function populateMapWithConstants(map: Map<string, Expr>, expr: Expr) {
    if (expr.numArgs() === 0 && expr.decl().kind() === Z3_decl_kind.Z3_OP_UNINTERPRETED) {
        map.set(expr.name() as string, expr);
    }
    for (const child of expr.children()) {
        populateMapWithConstants(map, child);
    }
}

export default {
    populateMapWithConstants
}