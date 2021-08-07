// --initial-memory a:[-3,3]
// --final-memory a:[-52,6]
// --disable-widening

a = a * 2;
loop {
  assume (-50 < a);
  a = a - 3
}
