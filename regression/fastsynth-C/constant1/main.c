int EXPRESSIONa(void);
int EXPRESSIONb(void);

int main()
{
  int asd;
  int x=nondet();
  __CPROVER_assume(x==4);
  asd=EXPRESSIONa();
  __CPROVER_assert(asd==1, "");

  asd=EXPRESSIONb();
  __CPROVER_assert(asd==2, "");
}
