// --initial-memory 'a=[5,15]'
// --final-memory   'a=[5,50]'
// --disable-widening

loop {
  assume ((a < 50) || (5 < b));
  a = a + 1
}

