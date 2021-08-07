// --initial-memory a:[-10,10]
// --final-memory a:[-5,33]
// --disable-widening

a = a + 5;
loop {
  assume (a < 30);
  a = a + 4
}
