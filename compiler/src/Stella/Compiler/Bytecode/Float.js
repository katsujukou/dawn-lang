// The byte order is written out rather than left to the platform: a typed array
// takes the host's, while a `DataView` takes the one it is given.
const view = new DataView(new ArrayBuffer(8));

export const halvesOfNumber = (n) => {
  view.setFloat64(0, n, true);
  return { lo: view.getInt32(0, true), hi: view.getInt32(4, true) };
};

export const numberOfHalves = (hi) => (lo) => {
  view.setInt32(0, lo, true);
  view.setInt32(4, hi, true);
  return view.getFloat64(0, true);
};
