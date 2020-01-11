struct Request {
  1: i32 x;
  2: i32 y;
}

struct Response {
  1: i32 z;
}

service Solver {
  Response solve(1: Request q);
}
