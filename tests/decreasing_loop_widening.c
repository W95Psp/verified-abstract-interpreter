// --initial-memory a:[-3,3]
// --final-memory a:[-64,6]

a = a * 2;
loop {
  assume (-50 < a);
  a = a - 3
}
