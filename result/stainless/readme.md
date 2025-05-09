# AVL Tree verified in Stainless

```shell
stainless LinkedList.scala
```

Expected output

```text
[  Info  ] Finished compiling                                       
[  Info  ] Preprocessing finished                                   
[  Info  ] Finished lowering the symbols                            
[  Info  ] Finished generating VCs                                  
[  Info  ] Starting verification...
[  Info  ]  Verified: 0 / 250
[Warning ] The Z3 native interface is not available. Falling back onto smt-z3.
[  Info  ]  Verified: 250 / 250                   
[  Info  ] Done in 121,33s
[  Info  ]   ┌───────────────────┐
[  Info  ] ╔═╡ stainless summary ╞══════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╗
[  Info  ] ║ └───────────────────┘                                                                                                                                          ║
[  Info  ] ║ AVLTree.scala:141:12:   LeafRequireForDefault         class invariant                                                         valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:143:12:   balance                       postcondition                                                           valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:263:13:   balance                       cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:263:31:   balance                       cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:267:11:   balance                       cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:267:38:   balance                       postcondition                                                           valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:267:38:   balance                       precond. (call rotateRightLeft(thiss) (require 1/5))                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:267:38:   balance                       precond. (call rotateRightLeft(thiss) (require 2/5))                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:267:38:   balance                       precond. (call rotateRightLeft(thiss) (require 3/5))                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:267:38:   balance                       precond. (call rotateRightLeft(thiss) (require 4/5))                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:267:38:   balance                       precond. (call rotateRightLeft(thiss) (require 5/5))                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:268:12:   balance                       postcondition                                                           valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:268:12:   balance                       precond. (call rotateLeft(thiss) (require 1/5))                         valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:268:12:   balance                       precond. (call rotateLeft(thiss) (require 2/5))                         valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:268:12:   balance                       precond. (call rotateLeft(thiss) (require 3/5))                         valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:268:12:   balance                       precond. (call rotateLeft(thiss) (require 4/5))                         valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:268:12:   balance                       precond. (call rotateLeft(thiss) (require 5/5))                         valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:270:11:   balance                       cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:270:36:   balance                       postcondition                                                           valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:270:36:   balance                       precond. (call rotateLeftRight(thiss) (require 1/5))                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:270:36:   balance                       precond. (call rotateLeftRight(thiss) (require 2/5))                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:270:36:   balance                       precond. (call rotateLeftRight(thiss) (require 3/5))                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:270:36:   balance                       precond. (call rotateLeftRight(thiss) (require 4/5))                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:270:36:   balance                       precond. (call rotateLeftRight(thiss) (require 5/5))                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:271:12:   balance                       postcondition                                                           valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:271:12:   balance                       precond. (call rotateRight(thiss) (require 1/5))                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:271:12:   balance                       precond. (call rotateRight(thiss) (require 2/5))                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:271:12:   balance                       precond. (call rotateRight(thiss) (require 3/5))                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:271:12:   balance                       precond. (call rotateRight(thiss) (require 4/5))                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:271:12:   balance                       precond. (call rotateRight(thiss) (require 5/5))                        valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:19:5:     balanceFactor                 body assertion: match exhaustiveness                                    trivial                     0,0  ║
[  Info  ] ║ AVLTree.scala:21:32:    balanceFactor                 body assertion: Subtraction overflow                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:74:7:     contains                      non-negative measure                                                    valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:76:5:     contains                      body assertion: match exhaustiveness                                    valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:76:5:     contains                      postcondition                                                           valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:77:22:    contains                      postcondition                                                           valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:79:21:    contains                      postcondition                                                           valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:80:25:    contains                      measure decreases                                                       valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:80:25:    contains                      postcondition                                                           valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:80:25:    contains                      precond. (call contains((scrut.left): @DropVCs , x))                    valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:81:14:    contains                      measure decreases                                                       valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:81:14:    contains                      postcondition                                                           valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:81:14:    contains                      precond. (call contains((scrut.right): @DropVCs , x))                   valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:8:7:      content                       non-negative measure                                                    valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:8:27:     content                       body assertion: match exhaustiveness                                    trivial                     0,0  ║
[  Info  ] ║ AVLTree.scala:10:30:    content                       measure decreases                                                       valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:10:53:    content                       measure decreases                                                       valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:7:23:     delete                        postcondition                                                           valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:109:7:    delete                        non-negative measure                                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:111:5:    delete                        body assertion: match exhaustiveness                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:111:5:    delete                        postcondition                                                           valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:115:11:   delete                        body assertion: match exhaustiveness                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:115:11:   delete                        postcondition                                                           valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:116:38:   delete                        class invariant                                                         valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:116:38:   delete                        postcondition                                                           valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:120:23:   delete                        precond. (call min(scrut._2) (require 1/2))                             valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:120:23:   delete                        precond. (call min(scrut._2) (require 2/2))                             valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:121:30:   delete                        measure decreases                                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:121:30:   delete                        precond. (call delete((scrut.right): @DropVCs , m))                     valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:122:15:   delete                        class invariant                                                         valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:122:15:   delete                        postcondition                                                           valid             U:smt-z3  11,9 ║
[  Info  ] ║ AVLTree.scala:122:15:   delete                        precond. (call balance(Node(m, (scrut.left): @DropVC... (require 1/5))  valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:122:15:   delete                        precond. (call balance(Node(m, (scrut.left): @DropVC... (require 2/5))  valid             U:smt-z3  0,8  ║
[  Info  ] ║ AVLTree.scala:122:15:   delete                        precond. (call balance(Node(m, (scrut.left): @DropVC... (require 3/5))  valid             U:smt-z3  0,5  ║
[  Info  ] ║ AVLTree.scala:122:15:   delete                        precond. (call balance(Node(m, (scrut.left): @DropVC... (require 4/5))  valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:122:15:   delete                        precond. (call balance(Node(m, (scrut.left): @DropVC... (require 5/5))  valid             U:smt-z3  1,0  ║
[  Info  ] ║ AVLTree.scala:122:36:   delete                        body assertion: Addition overflow                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:126:25:   delete                        measure decreases                                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:126:25:   delete                        precond. (call delete((scrut.left): @DropVCs , x))                      valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:127:11:   delete                        class invariant                                                         valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:127:11:   delete                        postcondition                                                           valid             U:smt-z3  12,9 ║
[  Info  ] ║ AVLTree.scala:127:11:   delete                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 1/5))  valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:127:11:   delete                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 2/5))  valid             U:smt-z3  1,0  ║
[  Info  ] ║ AVLTree.scala:127:11:   delete                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 3/5))  valid             U:smt-z3  1,0  ║
[  Info  ] ║ AVLTree.scala:127:11:   delete                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 4/5))  valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:127:11:   delete                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 5/5))  valid             U:smt-z3  0,7  ║
[  Info  ] ║ AVLTree.scala:127:31:   delete                        body assertion: Addition overflow                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:129:26:   delete                        measure decreases                                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:129:26:   delete                        precond. (call delete((scrut.right): @DropVCs , x))                     valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:130:11:   delete                        class invariant                                                         valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:130:11:   delete                        postcondition                                                           valid             U:smt-z3  9,0  ║
[  Info  ] ║ AVLTree.scala:130:11:   delete                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 1/5))  valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:130:11:   delete                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 2/5))  valid             U:smt-z3  1,1  ║
[  Info  ] ║ AVLTree.scala:130:11:   delete                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 3/5))  valid             U:smt-z3  0,5  ║
[  Info  ] ║ AVLTree.scala:130:11:   delete                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 4/5))  valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:130:11:   delete                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 5/5))  valid             U:smt-z3  0,7  ║
[  Info  ] ║ AVLTree.scala:130:32:   delete                        body assertion: Addition overflow                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:136:49:   delete                        body assertion: Subtraction overflow                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:136:49:   delete                        body assertion: Subtraction overflow                                    valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:136:49:   delete                        body assertion: Subtraction overflow                                    valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:136:49:   delete                        body assertion: Subtraction overflow                                    valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:136:49:   delete                        body assertion: Subtraction overflow                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:136:49:   delete                        body assertion: Subtraction overflow                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:136:49:   delete                        body assertion: Subtraction overflow                                    valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:136:49:   delete                        body assertion: Subtraction overflow                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:136:49:   delete                        body assertion: Subtraction overflow                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:146:3:    delete                        postcondition                                                           valid             U:smt-z3  0,2  ║
[  Info  ] ║ AVLTree.scala:147:3:    delete                        postcondition                                                           valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:36:7:     hasAVLTreeStructure           non-negative measure                                                    valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:36:38:    hasAVLTreeStructure           body assertion: match exhaustiveness                                    trivial                     0,0  ║
[  Info  ] ║ AVLTree.scala:39:7:     hasAVLTreeStructure           measure decreases                                                       valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:40:9:     hasAVLTreeStructure           measure decreases                                                       valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:45:19:    hasAVLTreeStructure           body assertion: Addition overflow                                       valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:45:24:    hasAVLTreeStructure           body assertion: match exhaustiveness                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:25:7:     hasBinarySearchTreeStructure  non-negative measure                                                    valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:25:47:    hasBinarySearchTreeStructure  body assertion: match exhaustiveness                                    trivial                     0,0  ║
[  Info  ] ║ AVLTree.scala:28:7:     hasBinarySearchTreeStructure  measure decreases                                                       valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:29:9:     hasBinarySearchTreeStructure  measure decreases                                                       valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:13:21:    height                        body assertion: match exhaustiveness                                    trivial                     0,0  ║
[  Info  ] ║ AVLTree.scala:7:23:     insert                        postcondition                                                           valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:86:7:     insert                        non-negative measure                                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:90:5:     insert                        body assertion: match exhaustiveness                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:90:5:     insert                        postcondition                                                           valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:91:22:    insert                        class invariant                                                         valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:91:22:    insert                        postcondition                                                           valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:91:30:    insert                        class invariant                                                         valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:91:38:    insert                        class invariant                                                         valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:95:25:    insert                        measure decreases                                                       valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:95:25:    insert                        precond. (call insert((scrut.left): @DropVCs , x) (require 1/2))        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:95:25:    insert                        precond. (call insert((scrut.left): @DropVCs , x) (require 2/2))        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:96:11:    insert                        class invariant                                                         valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:96:11:    insert                        postcondition                                                           valid             U:smt-z3  7,7  ║
[  Info  ] ║ AVLTree.scala:96:11:    insert                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 1/5))  valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:96:11:    insert                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 2/5))  valid             U:smt-z3  0,5  ║
[  Info  ] ║ AVLTree.scala:96:11:    insert                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 3/5))  valid             U:smt-z3  0,2  ║
[  Info  ] ║ AVLTree.scala:96:11:    insert                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 4/5))  valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:96:11:    insert                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 5/5))  valid             U:smt-z3  0,6  ║
[  Info  ] ║ AVLTree.scala:96:31:    insert                        body assertion: Addition overflow                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:98:26:    insert                        measure decreases                                                       valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:98:26:    insert                        precond. (call insert((scrut.right): @DropVCs , x) (require 1/2))       valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:98:26:    insert                        precond. (call insert((scrut.right): @DropVCs , x) (require 2/2))       valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:99:11:    insert                        class invariant                                                         valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:99:11:    insert                        postcondition                                                           valid             U:smt-z3  11,4 ║
[  Info  ] ║ AVLTree.scala:99:11:    insert                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 1/5))  valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:99:11:    insert                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 2/5))  valid             U:smt-z3  0,5  ║
[  Info  ] ║ AVLTree.scala:99:11:    insert                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 3/5))  valid             U:smt-z3  0,2  ║
[  Info  ] ║ AVLTree.scala:99:11:    insert                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 4/5))  valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:99:11:    insert                        precond. (call balance(Node((scrut.value): @DropVCs ... (require 5/5))  valid             U:smt-z3  0,6  ║
[  Info  ] ║ AVLTree.scala:99:32:    insert                        body assertion: Addition overflow                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:105:49:   insert                        body assertion: Addition overflow                                       valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:105:49:   insert                        body assertion: Addition overflow                                       valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:105:49:   insert                        body assertion: Addition overflow                                       valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:105:49:   insert                        body assertion: Addition overflow                                       valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:105:49:   insert                        body assertion: Addition overflow                                       valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:150:11:   inv                           cast correctness                                                        valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:150:11:   inv                           precond. (call inv(({   assert(thiss.isInstanceOf[No...)                valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:63:7:     isAVLTree                     non-negative measure                                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:63:28:    isAVLTree                     body assertion: match exhaustiveness                                    trivial                     0,0  ║
[  Info  ] ║ AVLTree.scala:66:7:     isAVLTree                     measure decreases                                                       valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:67:9:     isAVLTree                     measure decreases                                                       valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:52:7:     isBalanced                    non-negative measure                                                    valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:52:29:    isBalanced                    body assertion: match exhaustiveness                                    trivial                     0,0  ║
[  Info  ] ║ AVLTree.scala:55:7:     isBalanced                    measure decreases                                                       valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:56:9:     isBalanced                    measure decreases                                                       valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:145:3:    max                           postcondition                                                           valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:163:7:    max                           non-negative measure                                                    valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:165:5:    max                           body assertion: match exhaustiveness                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:165:5:    max                           postcondition                                                           valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:167:38:   max                           measure decreases                                                       valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:167:38:   max                           postcondition                                                           valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:167:38:   max                           precond. (call max((scrut.right): @DropVCs ) (require 1/2))             valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:167:38:   max                           precond. (call max((scrut.right): @DropVCs ) (require 2/2))             valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:170:5:    max                           precond. (call contains(thiss, res))                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:170:5:    max                           precond. (call contains(thiss, res))                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:170:5:    max                           precond. (call contains(thiss, res))                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:171:27:   max                           precond. (call contains(thiss, x))                                      valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:171:27:   max                           precond. (call contains(thiss, x))                                      valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:171:27:   max                           precond. (call contains(thiss, x))                                      valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:145:3:    min                           postcondition                                                           valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:152:7:    min                           non-negative measure                                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:154:5:    min                           body assertion: match exhaustiveness                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:154:5:    min                           postcondition                                                           valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:156:38:   min                           measure decreases                                                       valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:156:38:   min                           postcondition                                                           valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:156:38:   min                           precond. (call min((scrut.left): @DropVCs ) (require 1/2))              valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:156:38:   min                           precond. (call min((scrut.left): @DropVCs ) (require 2/2))              valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:177:13:   rotateLeft                    cast correctness                                                        valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:177:31:   rotateLeft                    cast correctness                                                        valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:178:35:   rotateLeft                    cast correctness                                                        valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:180:5:    rotateLeft                    body assertion: match exhaustiveness                                    valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:180:5:    rotateLeft                    cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:180:5:    rotateLeft                    postcondition                                                           valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:182:9:    rotateLeft                    class invariant                                                         valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:182:9:    rotateLeft                    postcondition                                                           valid             U:smt-z3  5,0  ║
[  Info  ] ║ AVLTree.scala:184:11:   rotateLeft                    class invariant                                                         valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:184:16:   rotateLeft                    cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:184:23:   rotateLeft                    cast correctness                                                        valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:184:33:   rotateLeft                    body assertion: Addition overflow                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:184:45:   rotateLeft                    cast correctness                                                        valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:186:11:   rotateLeft                    body assertion: Addition overflow                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:187:13:   rotateLeft                    body assertion: Addition overflow                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:187:25:   rotateLeft                    cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:217:13:   rotateLeftRight               cast correctness                                                        valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:217:31:   rotateLeftRight               cast correctness                                                        valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:218:36:   rotateLeftRight               cast correctness                                                        valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:220:5:    rotateLeftRight               body assertion: match exhaustiveness                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:220:5:    rotateLeftRight               cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:220:5:    rotateLeftRight               postcondition                                                           valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:222:9:    rotateLeftRight               body assertion: match exhaustiveness                                    valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:222:9:    rotateLeftRight               postcondition                                                           valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:224:13:   rotateLeftRight               class invariant                                                         valid             U:smt-z3  0,2  ║
[  Info  ] ║ AVLTree.scala:224:13:   rotateLeftRight               postcondition                                                           valid             U:smt-z3  18,7 ║
[  Info  ] ║ AVLTree.scala:226:15:   rotateLeftRight               class invariant                                                         valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:226:32:   rotateLeftRight               body assertion: Addition overflow                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:227:15:   rotateLeftRight               class invariant                                                         valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:227:20:   rotateLeftRight               cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:227:32:   rotateLeftRight               cast correctness                                                        valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:227:39:   rotateLeftRight               body assertion: Addition overflow                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:227:63:   rotateLeftRight               cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:228:15:   rotateLeftRight               body assertion: Addition overflow                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:229:17:   rotateLeftRight               body assertion: Addition overflow                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:230:17:   rotateLeftRight               body assertion: Addition overflow                                       valid             U:smt-z3  0,2  ║
[  Info  ] ║ AVLTree.scala:230:41:   rotateLeftRight               cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:197:13:   rotateRight                   cast correctness                                                        valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:197:31:   rotateRight                   cast correctness                                                        valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:198:36:   rotateRight                   cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:200:5:    rotateRight                   body assertion: match exhaustiveness                                    valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:200:5:    rotateRight                   cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:200:5:    rotateRight                   postcondition                                                           valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:202:9:    rotateRight                   class invariant                                                         valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:202:9:    rotateRight                   postcondition                                                           valid             U:smt-z3  6,8  ║
[  Info  ] ║ AVLTree.scala:205:11:   rotateRight                   class invariant                                                         valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:205:16:   rotateRight                   cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:205:27:   rotateRight                   cast correctness                                                        valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:205:34:   rotateRight                   body assertion: Addition overflow                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:205:57:   rotateRight                   cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:206:11:   rotateRight                   body assertion: Addition overflow                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:207:13:   rotateRight                   body assertion: Addition overflow                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:207:36:   rotateRight                   cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:240:13:   rotateRightLeft               cast correctness                                                        valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:240:31:   rotateRightLeft               cast correctness                                                        valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:241:35:   rotateRightLeft               cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:243:5:    rotateRightLeft               body assertion: match exhaustiveness                                    valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:243:5:    rotateRightLeft               cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:243:5:    rotateRightLeft               postcondition                                                           valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:245:9:    rotateRightLeft               body assertion: match exhaustiveness                                    valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:245:9:    rotateRightLeft               postcondition                                                           valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:247:13:   rotateRightLeft               class invariant                                                         valid             U:smt-z3  0,2  ║
[  Info  ] ║ AVLTree.scala:247:13:   rotateRightLeft               postcondition                                                           valid             U:smt-z3  11,1 ║
[  Info  ] ║ AVLTree.scala:249:15:   rotateRightLeft               class invariant                                                         valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:249:20:   rotateRightLeft               cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:249:27:   rotateRightLeft               cast correctness                                                        valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:249:38:   rotateRightLeft               body assertion: Addition overflow                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:249:50:   rotateRightLeft               cast correctness                                                        valid from cache            0,0  ║
[  Info  ] ║ AVLTree.scala:250:15:   rotateRightLeft               class invariant                                                         valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:250:32:   rotateRightLeft               body assertion: Addition overflow                                       valid             U:smt-z3  0,2  ║
[  Info  ] ║ AVLTree.scala:251:15:   rotateRightLeft               body assertion: Addition overflow                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:252:17:   rotateRightLeft               body assertion: Addition overflow                                       valid             U:smt-z3  0,1  ║
[  Info  ] ║ AVLTree.scala:252:29:   rotateRightLeft               cast correctness                                                        valid             U:smt-z3  0,0  ║
[  Info  ] ║ AVLTree.scala:253:17:   rotateRightLeft               body assertion: Addition overflow                                       valid             U:smt-z3  0,1  ║
[  Info  ] ╟┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄╢
[  Info  ] ║ total: 250  valid: 250  (38 from cache, 7 trivial) invalid: 0    unknown: 0    time:  113,34                                                                   ║
[  Info  ] ╚════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╝
[  Info  ] Verification pipeline summary:
[  Info  ]   cache, anti-aliasing, nativez3, non-batched
[  Info  ] Shutting down executor service.
```