import { Z3_decl_kind } from "./z3.js";
export function populateMapWithConstants(map, expr) {
    if (expr.numArgs() === 0 && expr.decl().kind() === Z3_decl_kind.Z3_OP_UNINTERPRETED) {
        map.set(expr.name(), expr);
    }
    for (const child of expr.children()) {
        populateMapWithConstants(map, child);
    }
}
export default {
    populateMapWithConstants
};
