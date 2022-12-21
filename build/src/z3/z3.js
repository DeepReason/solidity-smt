import { init, Z3_decl_kind, Z3_sort_kind, } from 'z3-solver';
let ctx;
let Z3C;
async function getContext() {
    if (ctx === undefined) {
        const { Z3, Context, } = await init();
        ctx = Context;
        Z3C = Z3;
    }
    return ctx;
}
let z3Mem;
async function makeZ3() {
    if (z3Mem === undefined)
        z3Mem = (await getContext())('main');
    return z3Mem;
}
export { Z3_decl_kind, Z3_sort_kind };
export default makeZ3;
