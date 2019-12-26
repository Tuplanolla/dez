struct Request {
  1: i32 x;
  2: i32 y;
}

struct Response {
  1: i32 z;
}

service Evaluator {
  i32 eval(1: i32 x, 2: i32 y);
}
