USING: ;

IN: fmc.types


! * W.H. Type system
TUPLE: funtype in out ;
C: <funtype> funtype

TUPLE: injtype in outs ;
C: <injtype> injtype

TUPLE: choicetype ins out ;
C: <choicetype> choicetype

TUPLE: type-var name ;
C: <type-var> type-var

! GENERIC: annotate-var-types ( term: fmc-term -- term: typed-fmc )
! M:
