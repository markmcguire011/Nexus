


val prog =
  PROGRAM
    {decls=["i","j"],
     stmts=[ST_EXP {exp=EXP_ASSIGN {lhs=EXP_ID "i",rhs=EXP_NUM 5}},
            ST_EXP {exp=EXP_ASSIGN {lhs=EXP_ID "j",rhs=EXP_NUM 5}},
            ST_BLOCK
              {stmts=[ST_BLOCK
                        {stmts=[ST_BLOCK
                                  {stmts=[ST_BLOCK
                                            {stmts=[ST_PRINT
                                                      {exp=EXP_BINARY
                                                             {lft=EXP_ID "j",
                                                              opr=BOP_PLUS,
                                                              rht=EXP_ID "i"}},
                                                    ST_PRINT
                                                      {exp=EXP_STRING "\n"},
                                                    ST_EXP
                                                      {exp=EXP_ASSIGN
                                                             {lhs=EXP_ID "j",
                                                              rhs=EXP_BINARY
                                                                    {lft=EXP_ID
                                                                           "j",
                                                                     opr=BOP_MINUS,
                                                                     rht=EXP_NUM
                                                                           1}}}]},
                                          ST_WHILE
                                            {body=ST_BLOCK
                                                    {stmts=[ST_PRINT
                                                              {exp=EXP_BINARY
                                                                     {lft=EXP_ID
                                                                            "j",
                                                                      opr=BOP_PLUS,
                                                                      rht=EXP_ID
                                                                            "i"}},
                                                            ST_PRINT
                                                              {exp=EXP_STRING
                                                                     "\n"},
                                                            ST_EXP
                                                              {exp=EXP_ASSIGN
                                                                     {lhs=EXP_ID
                                                                            "j",
                                                                      rhs=EXP_BINARY
                                                                            {lft=EXP_ID
                                                                                   "j",
                                                                             opr=BOP_MINUS,
                                                                             rht=EXP_NUM
                                                                                   1}}}]},
                                             guard=EXP_BINARY
                                                     {lft=EXP_ID "j",
                                                      opr=BOP_GT,
                                                      rht=EXP_NUM 0}}]},
                                ST_PRINT
                                  {exp=EXP_BINARY
                                         {lft=EXP_ID "j",opr=BOP_PLUS,
                                          rht=EXP_ID "i"}},
                                ST_EXP
                                  {exp=EXP_ASSIGN
                                         {lhs=EXP_ID "i",
                                          rhs=EXP_BINARY
                                                {lft=EXP_ID "i",opr=BOP_MINUS,
                                                 rht=EXP_NUM 1}}}]},
                      ST_WHILE
                        {body=ST_BLOCK
                                {stmts=[ST_BLOCK
                                          {stmts=[ST_BLOCK
                                                    {stmts=[ST_PRINT
                                                              {exp=EXP_BINARY
                                                                     {lft=EXP_ID
                                                                            "j",
                                                                      opr=BOP_PLUS,
                                                                      rht=EXP_ID
                                                                            "i"}},
                                                            ST_PRINT
                                                              {exp=EXP_STRING
                                                                     "\n"},
                                                            ST_EXP
                                                              {exp=EXP_ASSIGN
                                                                     {lhs=EXP_ID
                                                                            "j",
                                                                      rhs=EXP_BINARY
                                                                            {lft=EXP_ID
                                                                                   "j",
                                                                             opr=BOP_MINUS,
                                                                             rht=EXP_NUM
                                                                                   1}}}]},
                                                  ST_WHILE
                                                    {body=ST_BLOCK
                                                            {stmts=[ST_PRINT
                                                                      {exp=EXP_BINARY
                                                                             {lft=EXP_ID
                                                                                    "j",
                                                                              opr=BOP_PLUS,
                                                                              rht=EXP_ID
                                                                                    "i"}},
                                                                    ST_PRINT
                                                                      {exp=EXP_STRING
                                                                             "\n"},
                                                                    ST_EXP
                                                                      {exp=EXP_ASSIGN
                                                                             {lhs=EXP_ID
                                                                                    "j",
                                                                              rhs=EXP_BINARY
                                                                                    {lft=EXP_ID
                                                                                           "j",
                                                                                     opr=BOP_MINUS,
                                                                                     rht=EXP_NUM
                                                                                           1}}}]},
                                                     guard=EXP_BINARY
                                                             {lft=EXP_ID "j",
                                                              opr=BOP_GT,
                                                              rht=EXP_NUM 0}}]},
                                        ST_PRINT
                                          {exp=EXP_BINARY
                                                 {lft=EXP_ID "j",opr=BOP_PLUS,
                                                  rht=EXP_ID "i"}},
                                        ST_EXP
                                          {exp=EXP_ASSIGN
                                                 {lhs=EXP_ID "i",
                                                  rhs=EXP_BINARY
                                                        {lft=EXP_ID "i",
                                                         opr=BOP_MINUS,
                                                         rht=EXP_NUM 1}}}]},
                         guard=EXP_UNARY
                                 {opnd=EXP_BINARY
                                         {lft=EXP_ID "i",opr=BOP_LE,
                                          rht=EXP_NUM 0},opr=UOP_NOT}}]}]}
  : program

;
