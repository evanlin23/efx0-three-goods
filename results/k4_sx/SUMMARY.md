# proof/k4-sx: summed counters

Made by `python3 k4/sx_summary.py` from the complete logs under `results/k4_sx/`. Every log starts with the command that wrote it.

## Hunts for non-completable f = 1 keys (k4/sx_hunt.py on k4/red.c)

### n3_all (6 logs)

- distinct profiles with a non-completable key: 62208
- f1: 7284544
- key_noncompletable: 62208
- keys: 14256832
- profiles: 299837376

### n4_2_r20k (1 logs)

- distinct profiles with a non-completable key: 0
- f1: 165045
- key_noncompletable: 0
- keys: 303564
- profiles: 6180000

### n4_3_r40k (1 logs)

- distinct profiles with a non-completable key: 59
- f1: 551666
- key_noncompletable: 59
- keys: 1044381
- profiles: 13560000

### n4_pure_r40k (1 logs)

- distinct profiles with a non-completable key: 240
- f1: 430765
- key_noncompletable: 240
- keys: 844132
- profiles: 8760000

### n5_n4_2_r200 (1 logs)

- distinct profiles with a non-completable key: 0
- f1: 10719
- key_noncompletable: 0
- keys: 19971
- profiles: 1093600

### n5_n4_3_r200 (5 logs)

- distinct profiles with a non-completable key: 0
- f1: 51240
- key_noncompletable: 0
- keys: 96226
- profiles: 1972200

### n5_n4_4_r200 (5 logs)

- distinct profiles with a non-completable key: 0
- f1: 82386
- key_noncompletable: 0
- keys: 157244
- profiles: 1969200

### n5_pure_r1000 (5 logs)

- distinct profiles with a non-completable key: 11
- f1: 263852
- key_noncompletable: 11
- keys: 516100
- profiles: 4674000

### total

- distinct profiles with a non-completable key: 62518
- f1: 8840217
- key_noncompletable: 62518
- keys: 17238450
- profiles: 338046376

## Repair lemmas at the Z′-maxima of the non-completable f = 1 keys (k4/sx_zprime.py)

### n3_all (17 logs)

- MAIN CASE A: 104372
- MAIN CASE B1: 7824
- MAIN CASE C: 4052
- Zmax: 116248
- keys: 62208
- keys xtype=BT: 14880
- keys xtype=bc: 5072
- keys xtype=bcbd: 13264
- keys xtype=flat: 28992
- regime I: 108424
- regime I GPM ok k=1 adjacent(T3)=True: 25440
- regime I GPM paths k=1 leaf kind=Tg: 25440
- regime I OS o theta-b=False: 131448
- regime I OS o theta-b=True: 27944
- regime I OS succeeds: 108424
- regime I OS theta-b: exact def(P')<def* False, OSd bundle value 4 (omega+2=5), T=several: 1200
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 3 (omega+2=4), T=several: 5792
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 4 (omega+2=5), T=several: 17392
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=4), T=several: 1992
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=5), T=several: 1568
- regime I Prop C applies=False (only (H) missing=False): 85972
- regime I Prop C applies=True (only (H) missing=False): 22452
- regime I Prop C' applies=False (only (H') missing=False): 85428
- regime I Prop C' applies=True (only (H') missing=False): 22996
- regime I Zmax with a direct T3 move: 108424
- regime I cases A*,C,C': 4052
- regime I cases A,A*: 59092
- regime I cases A,A*,B1: 25440
- regime I cases A,A*,C: 896
- regime I cases A,A*,C': 1440
- regime I cases A,A*,C,C': 17504
- regime I direct kind ('zT', '-', 'own=V'): 6240
- regime I direct kind ('zT', '-', 'own=x'): 18720
- regime I direct kind ('zT', 'hV', 'own=V'): 12640
- regime I direct kind ('zT', 'hV', 'own=x'): 24800
- regime I direct kind ('zV', '-', 'own=V'): 30744
- regime I direct kind ('zV', '-', 'own=other'): 12640
- regime I direct kind ('zV', '-', 'own=x'): 103012
- regime I direct kind ('zV', 'h', 'own=other'): 13440
- regime I direct kind ('zV', 'h', 'own=x'): 44304
- regime I direct kind ('zV', 'hV', 'own=V'): 32384
- regime I direct kind ('zV', 'hV', 'own=x'): 56632
- regime I |V|=1 |T|=1 |VT|=1 t=0 x=BT: 25632
- regime I |V|=1 |T|=2 |VT|=1 t=0 x=bc: 13760
- regime I |V|=1 |T|=2 |VT|=1 t=0 x=bcbd: 9280
- regime I |V|=1 |T|=2 |VT|=1 t=0 x=flat: 2400
- regime I |V|=2 |T|=1 |VT|=1 t=1 x=BT: 6384
- regime I |V|=2 |T|=2 |VT|=2 t=0 x=bcbd: 7120
- regime I |V|=2 |T|=2 |VT|=2 t=0 x=flat: 18012
- regime I |V|=2 |T|=2 |VT|=2 t=1 x=bc: 1960
- regime I |V|=2 |T|=2 |VT|=2 t=1 x=bcbd: 6520
- regime I |V|=2 |T|=2 |VT|=2 t=1 x=flat: 17356
- regime II: 7824
- regime II GPM ok k=1 adjacent(T3)=True: 7824
- regime II GPM paths k=1 leaf kind=D: 6240
- regime II GPM paths k=1 leaf kind=R: 1584
- regime II OS succeeds: 0
- regime II Prop C applies=False (only (H) missing=False): 7824
- regime II Prop C' applies=False (only (H') missing=False): 7824
- regime II Zmax with a direct T3 move: 7824
- regime II cases B1: 7824
- regime II direct kind ('zT', '-', 'own=V'): 2160
- regime II direct kind ('zT', 'hV', 'own=V'): 1392
- regime II direct kind ('zT', 'hV', 'own=x'): 7824
- regime II |V|=1 |T|=1 |VT|=0 t=0 x=BT: 7824

### n4_3_r40k (1 logs)

- MAIN CASE A: 148
- MAIN CASE B1: 42
- MAIN CASE C': 1
- Zmax: 191
- keys: 59
- keys xtype=bcbd: 1
- keys xtype=flat: 58
- regime I: 191
- regime I GPM ok k=1 adjacent(T3)=True: 80
- regime I GPM paths k=1 leaf kind=R: 1
- regime I GPM paths k=1 leaf kind=R s in L: 2
- regime I GPM paths k=1 leaf kind=T3: 67
- regime I GPM paths k=1 leaf kind=Tg: 12
- regime I OS o theta-b=False: 195
- regime I OS o theta-b=True: 105
- regime I OS succeeds: 191
- regime I OS theta-b: exact def(P')<def* False, OSd bundle value 4 (omega+2=5), T=several: 3
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 3 (omega+2=4), T=several: 70
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 4 (omega+2=5), T=several: 16
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=4), T=several: 14
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=5), T=several: 2
- regime I Prop B' (modified path move) k=1 works=True: 2
- regime I Prop B' k=1 hypothesis (y valued only by x) holds=True: 2
- regime I Prop C applies=False (only (H) missing=False): 93
- regime I Prop C applies=True (only (H) missing=False): 98
- regime I Prop C' applies=False (only (H') missing=False): 187
- regime I Prop C' applies=False (only (H') missing=True): 2
- regime I Prop C' applies=True (only (H') missing=False): 2
- regime I Zmax with a direct T3 move: 191
- regime I cases A*,B1,C: 42
- regime I cases A*,C': 1
- regime I cases A,A*: 51
- regime I cases A,A*,B1: 38
- regime I cases A,A*,B1',Rs: 2
- regime I cases A,A*,C: 54
- regime I cases A,A*,C': 1
- regime I cases A,A*,C,C-H: 2
- regime I direct kind ('zT', '-', 'own=V'): 82
- regime I direct kind ('zT', '-', 'own=x'): 49
- regime I direct kind ('zT', 'hV', 'own=V'): 78
- regime I direct kind ('zT', 'hV', 'own=x'): 82
- regime I direct kind ('zV', '-', 'own=V'): 93
- regime I direct kind ('zV', '-', 'own=other'): 12
- regime I direct kind ('zV', '-', 'own=x'): 182
- regime I direct kind ('zV', 'h', 'own=V'): 67
- regime I direct kind ('zV', 'h', 'own=other'): 12
- regime I direct kind ('zV', 'h', 'own=x'): 51
- regime I direct kind ('zV', 'hV', 'own=V'): 96
- regime I direct kind ('zV', 'hV', 'own=other'): 4
- regime I direct kind ('zV', 'hV', 'own=x'): 119
- regime I |V|=2 |T|=2 |VT|=1 t=0 x=flat: 50
- regime I |V|=2 |T|=2 |VT|=1 t=1 x=flat: 32
- regime I |V|=2 |T|=2 |VT|=2 t=0 x=flat: 38
- regime I |V|=2 |T|=2 |VT|=2 t=1 x=flat: 29
- regime I |V|=3 |T|=2 |VT|=2 t=1 x=bcbd: 3
- regime I |V|=3 |T|=2 |VT|=2 t=1 x=flat: 39

### n4_pure_r40k (1 logs)

- MAIN CASE A: 346
- MAIN CASE B1: 16
- MAIN CASE B1': 6
- MAIN CASE C: 5
- MAIN CASE C': 1
- Zmax: 374
- keys: 240
- keys xtype=bc: 11
- keys xtype=bcbd: 30
- keys xtype=flat: 199
- regime I: 362
- regime I GPM ok k=1 adjacent(T3)=True: 40
- regime I GPM ok k=2 adjacent(T3)=True: 4
- regime I GPM paths k=1 leaf kind=D: 7
- regime I GPM paths k=1 leaf kind=R: 3
- regime I GPM paths k=1 leaf kind=R s in L: 2
- regime I GPM paths k=1 leaf kind=T4: 2
- regime I GPM paths k=1 leaf kind=Tg: 28
- regime I GPM paths k=2 leaf kind=Tg: 4
- regime I OS o theta-b=False: 485
- regime I OS o theta-b=True: 205
- regime I OS succeeds: 361
- regime I OS theta-b: exact def(P')<def* False, OSd bundle value 4 (omega+2=5), T=several: 6
- regime I OS theta-b: exact def(P')<def* False, OSd bundle value 5 (omega+2=6), T=several: 7
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 3 (omega+2=4), T=several: 34
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 4 (omega+2=5), T=several: 45
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 5 (omega+2=6), T=several: 82
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=4), T=several: 16
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=5), T=several: 6
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=6), T=several: 9
- regime I Prop B' (modified path move) k=1 works=True: 2
- regime I Prop B' k=1 hypothesis (y valued only by x) holds=False: 2
- regime I Prop C applies=False (only (H) missing=False): 205
- regime I Prop C applies=False (only (H) missing=True): 1
- regime I Prop C applies=True (only (H) missing=False): 156
- regime I Prop C' applies=False (only (H') missing=False): 335
- regime I Prop C' applies=False (only (H') missing=True): 3
- regime I Prop C' applies=True (only (H') missing=False): 24
- regime I Zmax with a direct T3 move: 362
- regime I cases A*,B1,C: 9
- regime I cases A*,C': 1
- regime I cases A*,C,C': 4
- regime I cases A*,C,C',C-H: 1
- regime I cases A,A*: 155
- regime I cases A,A*,B1: 26
- regime I cases A,A*,B1,C: 4
- regime I cases A,A*,Bk-adj: 4
- regime I cases A,A*,C: 131
- regime I cases A,A*,C': 16
- regime I cases A,A*,C,C',C-H: 2
- regime I cases A,A*,C,C-H: 5
- regime I cases A,A*,C-H: 1
- regime I cases A,A*,Rs: 2
- regime I cases B1: 1
- regime I direct kind ('zT', '-', 'own=V'): 25
- regime I direct kind ('zT', '-', 'own=x'): 28
- regime I direct kind ('zT', 'h', 'own=V'): 4
- regime I direct kind ('zT', 'h', 'own=other'): 4
- regime I direct kind ('zT', 'h', 'own=x'): 4
- regime I direct kind ('zT', 'hV', 'own=V'): 30
- regime I direct kind ('zT', 'hV', 'own=x'): 39
- regime I direct kind ('zV', '-', 'own=V'): 273
- regime I direct kind ('zV', '-', 'own=x'): 319
- regime I direct kind ('zV', 'h', 'own=V'): 71
- regime I direct kind ('zV', 'h', 'own=other'): 2
- regime I direct kind ('zV', 'h', 'own=x'): 86
- regime I direct kind ('zV', 'hV', 'own=V'): 296
- regime I direct kind ('zV', 'hV', 'own=other'): 9
- regime I direct kind ('zV', 'hV', 'own=x'): 335
- regime I |V|=1 |T|=2 |VT|=1 t=0 x=flat: 4
- regime I |V|=2 |T|=2 |VT|=1 t=0 x=flat: 8
- regime I |V|=2 |T|=2 |VT|=1 t=1 x=flat: 24
- regime I |V|=2 |T|=2 |VT|=2 t=0 x=flat: 40
- regime I |V|=2 |T|=2 |VT|=2 t=1 x=flat: 37
- regime I |V|=2 |T|=3 |VT|=2 t=0 x=flat: 4
- regime I |V|=2 |T|=3 |VT|=2 t=1 x=flat: 6
- regime I |V|=3 |T|=2 |VT|=2 t=1 x=bc: 15
- regime I |V|=3 |T|=2 |VT|=2 t=1 x=bcbd: 36
- regime I |V|=3 |T|=2 |VT|=2 t=1 x=flat: 186
- regime I |V|=3 |T|=3 |VT|=3 t=1 x=flat: 2
- regime II: 12
- regime II GPM ok k=1 adjacent(T3)=True: 6
- regime II GPM ok k=2 adjacent(T3)=True: 6
- regime II GPM paths k=1 leaf kind=R: 6
- regime II GPM paths k=1 leaf kind=R s in L: 6
- regime II GPM paths k=2 leaf kind=R: 6
- regime II GPM paths k=2 leaf kind=R s in L: 6
- regime II OS succeeds: 0
- regime II Prop B' (modified path move) k=1 works=True: 6
- regime II Prop B' (modified path move) k=2 works=True: 6
- regime II Prop B' k=1 hypothesis (y valued only by x) holds=True: 6
- regime II Prop B' k=2 hypothesis (y valued only by x) holds=True: 6
- regime II Prop C applies=False (only (H) missing=False): 12
- regime II Prop C' applies=False (only (H') missing=False): 12
- regime II Zmax with a direct T3 move: 12
- regime II cases B1',Bk',Rs: 6
- regime II cases B1,Bk-adj: 6
- regime II direct kind ('zT', '-', 'own=V'): 8
- regime II direct kind ('zT', '-', 'own=x'): 8
- regime II direct kind ('zT', 'h', 'own=V'): 8
- regime II direct kind ('zT', 'h', 'own=x'): 8
- regime II direct kind ('zT', 'hV', 'own=V'): 4
- regime II direct kind ('zT', 'hV', 'own=other'): 12
- regime II direct kind ('zT', 'hV', 'own=x'): 12
- regime II |V|=1 |T|=2 |VT|=0 t=0 x=bcbd: 12

### n5_pure_r1000 (2 logs)

- MAIN CASE A: 13
- Zmax: 13
- keys: 11
- keys xtype=bcbd: 2
- keys xtype=flat: 9
- regime I: 13
- regime I GPM ok k=1 adjacent(T3)=True: 4
- regime I GPM paths k=1 leaf kind=R: 1
- regime I GPM paths k=1 leaf kind=Tg: 3
- regime I OS o theta-b=False: 21
- regime I OS o theta-b=True: 1
- regime I OS succeeds: 13
- regime I OS theta-b: exact def(P')<def* False, OSd bundle value 5 (omega+2=6), T=several: 1
- regime I Prop C applies=False (only (H) missing=False): 13
- regime I Prop C' applies=False (only (H') missing=False): 12
- regime I Prop C' applies=True (only (H') missing=False): 1
- regime I Zmax with a direct T3 move: 13
- regime I cases A,A*: 8
- regime I cases A,A*,B1: 4
- regime I cases A,A*,C': 1
- regime I direct kind ('zT', '-', 'own=V'): 4
- regime I direct kind ('zT', '-', 'own=x'): 3
- regime I direct kind ('zT', 'hV', 'own=V'): 4
- regime I direct kind ('zT', 'hV', 'own=x'): 4
- regime I direct kind ('zV', '-', 'own=V'): 8
- regime I direct kind ('zV', '-', 'own=x'): 13
- regime I direct kind ('zV', 'hV', 'own=V'): 9
- regime I direct kind ('zV', 'hV', 'own=x'): 13
- regime I |V|=3 |T|=2 |VT|=1 t=1 x=flat: 4
- regime I |V|=4 |T|=2 |VT|=2 t=1 x=bcbd: 2
- regime I |V|=4 |T|=2 |VT|=2 t=1 x=flat: 7

### total

- MAIN CASE A: 104879
- MAIN CASE B1: 7882
- MAIN CASE B1': 6
- MAIN CASE C: 4057
- MAIN CASE C': 2
- Zmax: 116826
- keys: 62518
- keys xtype=BT: 14880
- keys xtype=bc: 5083
- keys xtype=bcbd: 13297
- keys xtype=flat: 29258
- regime I: 108990
- regime I GPM ok k=1 adjacent(T3)=True: 25564
- regime I GPM ok k=2 adjacent(T3)=True: 4
- regime I GPM paths k=1 leaf kind=D: 7
- regime I GPM paths k=1 leaf kind=R: 5
- regime I GPM paths k=1 leaf kind=R s in L: 4
- regime I GPM paths k=1 leaf kind=T3: 67
- regime I GPM paths k=1 leaf kind=T4: 2
- regime I GPM paths k=1 leaf kind=Tg: 25483
- regime I GPM paths k=2 leaf kind=Tg: 4
- regime I OS o theta-b=False: 132149
- regime I OS o theta-b=True: 28255
- regime I OS succeeds: 108989
- regime I OS theta-b: exact def(P')<def* False, OSd bundle value 4 (omega+2=5), T=several: 1209
- regime I OS theta-b: exact def(P')<def* False, OSd bundle value 5 (omega+2=6), T=several: 8
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 3 (omega+2=4), T=several: 5896
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 4 (omega+2=5), T=several: 17453
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 5 (omega+2=6), T=several: 82
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=4), T=several: 2022
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=5), T=several: 1576
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=6), T=several: 9
- regime I Prop B' (modified path move) k=1 works=True: 4
- regime I Prop B' k=1 hypothesis (y valued only by x) holds=False: 2
- regime I Prop B' k=1 hypothesis (y valued only by x) holds=True: 2
- regime I Prop C applies=False (only (H) missing=False): 86283
- regime I Prop C applies=False (only (H) missing=True): 1
- regime I Prop C applies=True (only (H) missing=False): 22706
- regime I Prop C' applies=False (only (H') missing=False): 85962
- regime I Prop C' applies=False (only (H') missing=True): 5
- regime I Prop C' applies=True (only (H') missing=False): 23023
- regime I Zmax with a direct T3 move: 108990
- regime I cases A*,B1,C: 51
- regime I cases A*,C': 2
- regime I cases A*,C,C': 4056
- regime I cases A*,C,C',C-H: 1
- regime I cases A,A*: 59306
- regime I cases A,A*,B1: 25508
- regime I cases A,A*,B1',Rs: 2
- regime I cases A,A*,B1,C: 4
- regime I cases A,A*,Bk-adj: 4
- regime I cases A,A*,C: 1081
- regime I cases A,A*,C': 1458
- regime I cases A,A*,C,C': 17504
- regime I cases A,A*,C,C',C-H: 2
- regime I cases A,A*,C,C-H: 7
- regime I cases A,A*,C-H: 1
- regime I cases A,A*,Rs: 2
- regime I cases B1: 1
- regime I direct kind ('zT', '-', 'own=V'): 6351
- regime I direct kind ('zT', '-', 'own=x'): 18800
- regime I direct kind ('zT', 'h', 'own=V'): 4
- regime I direct kind ('zT', 'h', 'own=other'): 4
- regime I direct kind ('zT', 'h', 'own=x'): 4
- regime I direct kind ('zT', 'hV', 'own=V'): 12752
- regime I direct kind ('zT', 'hV', 'own=x'): 24925
- regime I direct kind ('zV', '-', 'own=V'): 31118
- regime I direct kind ('zV', '-', 'own=other'): 12652
- regime I direct kind ('zV', '-', 'own=x'): 103526
- regime I direct kind ('zV', 'h', 'own=V'): 138
- regime I direct kind ('zV', 'h', 'own=other'): 13454
- regime I direct kind ('zV', 'h', 'own=x'): 44441
- regime I direct kind ('zV', 'hV', 'own=V'): 32785
- regime I direct kind ('zV', 'hV', 'own=other'): 13
- regime I direct kind ('zV', 'hV', 'own=x'): 57099
- regime I |V|=1 |T|=1 |VT|=1 t=0 x=BT: 25632
- regime I |V|=1 |T|=2 |VT|=1 t=0 x=bc: 13760
- regime I |V|=1 |T|=2 |VT|=1 t=0 x=bcbd: 9280
- regime I |V|=1 |T|=2 |VT|=1 t=0 x=flat: 2404
- regime I |V|=2 |T|=1 |VT|=1 t=1 x=BT: 6384
- regime I |V|=2 |T|=2 |VT|=1 t=0 x=flat: 58
- regime I |V|=2 |T|=2 |VT|=1 t=1 x=flat: 56
- regime I |V|=2 |T|=2 |VT|=2 t=0 x=bcbd: 7120
- regime I |V|=2 |T|=2 |VT|=2 t=0 x=flat: 18090
- regime I |V|=2 |T|=2 |VT|=2 t=1 x=bc: 1960
- regime I |V|=2 |T|=2 |VT|=2 t=1 x=bcbd: 6520
- regime I |V|=2 |T|=2 |VT|=2 t=1 x=flat: 17422
- regime I |V|=2 |T|=3 |VT|=2 t=0 x=flat: 4
- regime I |V|=2 |T|=3 |VT|=2 t=1 x=flat: 6
- regime I |V|=3 |T|=2 |VT|=1 t=1 x=flat: 4
- regime I |V|=3 |T|=2 |VT|=2 t=1 x=bc: 15
- regime I |V|=3 |T|=2 |VT|=2 t=1 x=bcbd: 39
- regime I |V|=3 |T|=2 |VT|=2 t=1 x=flat: 225
- regime I |V|=3 |T|=3 |VT|=3 t=1 x=flat: 2
- regime I |V|=4 |T|=2 |VT|=2 t=1 x=bcbd: 2
- regime I |V|=4 |T|=2 |VT|=2 t=1 x=flat: 7
- regime II: 7836
- regime II GPM ok k=1 adjacent(T3)=True: 7830
- regime II GPM ok k=2 adjacent(T3)=True: 6
- regime II GPM paths k=1 leaf kind=D: 6240
- regime II GPM paths k=1 leaf kind=R: 1590
- regime II GPM paths k=1 leaf kind=R s in L: 6
- regime II GPM paths k=2 leaf kind=R: 6
- regime II GPM paths k=2 leaf kind=R s in L: 6
- regime II OS succeeds: 0
- regime II Prop B' (modified path move) k=1 works=True: 6
- regime II Prop B' (modified path move) k=2 works=True: 6
- regime II Prop B' k=1 hypothesis (y valued only by x) holds=True: 6
- regime II Prop B' k=2 hypothesis (y valued only by x) holds=True: 6
- regime II Prop C applies=False (only (H) missing=False): 7836
- regime II Prop C' applies=False (only (H') missing=False): 7836
- regime II Zmax with a direct T3 move: 7836
- regime II cases B1: 7824
- regime II cases B1',Bk',Rs: 6
- regime II cases B1,Bk-adj: 6
- regime II direct kind ('zT', '-', 'own=V'): 2168
- regime II direct kind ('zT', '-', 'own=x'): 8
- regime II direct kind ('zT', 'h', 'own=V'): 8
- regime II direct kind ('zT', 'h', 'own=x'): 8
- regime II direct kind ('zT', 'hV', 'own=V'): 1396
- regime II direct kind ('zT', 'hV', 'own=other'): 12
- regime II direct kind ('zT', 'hV', 'own=x'): 7836
- regime II |V|=1 |T|=1 |VT|=0 t=0 x=BT: 7824
- regime II |V|=1 |T|=2 |VT|=0 t=0 x=bcbd: 12

## Lemma A⁺ at f ≥ 2 (k4/sx_f2.py)

### keys_rt4_n5b (1 logs)

- DLK_T3 FAIL f=3: 2
- DLK_T3T4 FAIL f=3: 2
- SKG_T3 fail f=3: 2
- SKG_T3T4 fail f=3: 2
- keys def*>0 f=3: 15
- keys f=3: 35
- keys f=3 def*=-1: 20
- keys f=3 def*=1: 15
- profiles: 2
- profiles f=3: 2
- profiles f>=1, omega>=1: 2
- profiles with a key def*>0 f=3: 2

### keys_rt4_n5c (1 logs)

- DLK_T3 FAIL f=3: 8
- DLK_T3T4 FAIL f=3: 8
- SKG_T3 fail f=3: 8
- SKG_T3T4 fail f=3: 8
- keys def*>0 f=3: 26
- keys f=3: 74
- keys f=3 def*=-1: 36
- keys f=3 def*=0: 12
- keys f=3 def*=1: 26
- profiles: 8
- profiles f=3: 8
- profiles f>=1, omega>=1: 8
- profiles with a key def*>0 f=3: 8

### rt4_n5b (1 logs)

- A+ applies, chain length j=0: 24
- A+ applies, chain length j=1: 57
- Zmax: 81
- Zmax: Lemma A+ applies=True: 81
- Zmax: direct T3 move=False, direct T3+ move=True, direct T4 move=False: 15
- Zmax: direct T3 move=True, direct T3+ move=True, direct T4 move=False: 66
- Zmax: free-valid owner exists=True: 81
- free-valid owner: frozen agents threatened=1: 162
- keys f=3: 15
- keys: Lemma A+ at some Zmax=True: 15
- profiles f=3: 2

### rt4_n5c (1 logs)

- A+ applies, chain length j=0: 54
- A+ applies, chain length j=1: 32
- A+ chain found but theta fails: 35
- Zmax: 118
- Zmax: Lemma A+ applies=False: 32
- Zmax: Lemma A+ applies=True: 86
- Zmax: direct T3 move=False, direct T3+ move=True, direct T4 move=False: 25
- Zmax: direct T3 move=True, direct T3+ move=True, direct T4 move=False: 93
- Zmax: free-valid owner exists=True: 118
- free-valid owner: frozen agents threatened=1: 173
- free-valid owner: frozen agents threatened=2: 35
- keys f=3: 26
- keys: Lemma A+ at some Zmax=False: 7
- keys: Lemma A+ at some Zmax=True: 19
- profiles f=3: 8

### total

- A+ applies, chain length j=0: 78
- A+ applies, chain length j=1: 89
- A+ chain found but theta fails: 35
- DLK_T3 FAIL f=3: 10
- DLK_T3T4 FAIL f=3: 10
- SKG_T3 fail f=3: 10
- SKG_T3T4 fail f=3: 10
- Zmax: 199
- Zmax: Lemma A+ applies=False: 32
- Zmax: Lemma A+ applies=True: 167
- Zmax: direct T3 move=False, direct T3+ move=True, direct T4 move=False: 40
- Zmax: direct T3 move=True, direct T3+ move=True, direct T4 move=False: 159
- Zmax: free-valid owner exists=True: 199
- free-valid owner: frozen agents threatened=1: 335
- free-valid owner: frozen agents threatened=2: 35
- keys def*>0 f=3: 41
- keys f=3: 150
- keys f=3 def*=-1: 56
- keys f=3 def*=0: 12
- keys f=3 def*=1: 41
- keys: Lemma A+ at some Zmax=False: 7
- keys: Lemma A+ at some Zmax=True: 34
- profiles: 10
- profiles f=3: 20
- profiles f>=1, omega>=1: 10
- profiles with a key def*>0 f=3: 10

