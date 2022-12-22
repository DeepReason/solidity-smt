import { Context, ContextCtor, init } from "z3-solver";

export * from 'z3-solver';

let ctx: undefined | ContextCtor;
let Z3C: any;

async function getContext(): Promise<ContextCtor> {
  if (ctx === undefined) {
    const {
      Z3,
      Context,
    } = await init();
    ctx = Context;
    Z3C = Z3;
  }
  return ctx;
}

export type Z3Obj = Context<'main'>;

let z3Mem: Z3Obj;

export async function makeZ3(): Promise<Z3Obj> {
  if (z3Mem === undefined) z3Mem = (await getContext())('main');
  return z3Mem;
}

export default makeZ3;