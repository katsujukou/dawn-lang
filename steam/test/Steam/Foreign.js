// A host function that throws where it is applied. An adapter built in PureScript
// cannot express this separately — an `EffectFn1` is applied and run at one moment —
// so the case that pins the exception boundary is written here.
export const throwsOnCall = (_args) => {
  throw new Error("thrown where it was called");
};
