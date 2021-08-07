// --initial-memory 'a=[5,15]; b=[5,15]'
// --final-memory   'a=T; b=T;c=T;d=T'

loop {
  assume ((a < 50) || (b < 50));
  a = a + 1;
  b = b + 1
}

