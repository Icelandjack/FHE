declare i8* @malloc(i32)
declare void @free(i8*)
declare i32 @printf(i8*, ...) nounwind
declare i32 @puts(i8*)
@fmt  = internal constant [5 x i8] c"%d, \00"
@nil  = internal constant [1 x i8] c"\00"


; :
%Foo = type { i32 }

; declare i8* @malloc(i32)
; declare void @free(i8*)

@veca   = global [5 x i32] [i32 1,  i32 2,  i32 3,  i32 4,  i32 5 ]
@vecb   = global [5 x i32] [i32 10, i32 20, i32 30, i32 40, i32 50]

%Listi = type { i32, i32* }

define void @nl() {
  call i32 @puts(i8* getelementptr([1 x i8]* @nil, i32 0, i32 0))
  ret void
}

define void @butt(i32 %x) {
  call i32 (i8*, ...)* @printf(i8* getelementptr([5 x i8]* @fmt, i32 0, i32 0), i32 %x)
  ret void
}

define void @vadd(i32* %a, i32* %b, i32* %c)
{
pre:
  br label %loop

loop:
  %i.1  = phi i32 [ 0,    %pre  ],
                  [ %i.2, %loop ]
  %i.2  = add i32 %i.1, 1

  %aPtr = getelementptr i32* %a, i32 %i.1
  %bPtr = getelementptr i32* %b, i32 %i.1
  %cPtr = getelementptr i32* %c, i32 %i.1

  %aVal = load i32* %aPtr
  %bVal = load i32* %bPtr
  %cVal = add  i32  %aVal, %bVal

  store i32 %cVal, i32* %cPtr
  ; store i32 42, i32* %cPtr

  %cond = icmp eq i32 %i.1, 4
  br i1 %cond, label %post, label %loop

post:
  call void @nl()
  ret void
}

define void @printVec(i32* %v)
{
pre: 
  br label %loop

loop:
  %i1 = phi i32 [ 0,   %pre  ],
                [ %i2, %loop ]

  %i2 = add i32 %i1, 1
  %ptr1 = getelementptr i32* %v, i32 %i1
  %val1 = load i32* %ptr1

  call void @butt(i32 %val1)

  %cmp = icmp eq i32 %i1, 4
  br i1 %cmp, label %post, label %loop

post:
  call void @nl()
  ret void
}

; %Listi = type { i32, i32* }
define void @printVec2(%Listi* %listi)
{
pre:
  %pListi = getelementptr %Listi* %listi, i32 0, i32 0
  %num    = load i32* %pListi
  call void @butt(i32 %num)
  call void @nl()


  br label %post

; define void @allocate() nounwind {
;     %1 = call i8* @malloc(i32 4)
;     %foo = bitcast i8* %1 to %Foo*
;     %2 = getelementptr %Foo* %foo, i32 0, i32 0
;     store i32 12, i32* %2
;     call void @free(i8* %1)
;     ret void
; }



; pre: 
;   br label %loop

; loop:
;   %i1 = phi i32 [ 0,   %pre  ],
;                 [ %i2, %loop ]

;   %i2 = add i32 %i1, 1
;   %ptr1 = getelementptr i32* %v, i32 %i1
;   %val1 = load i32* %ptr1

;   call void @butt(i32 %val1)

;   %cmp = icmp eq i32 %i1, 4
;   br i1 %cmp, label %post, label %loop

post:
;   call void @nl()
  ret void
}


define i32 @main()
{
  %pA  = getelementptr [5 x i32]* @veca, i64 0, i32 0
  %pB  = getelementptr [5 x i32]* @vecb, i64 0, i32 0
  %pC  = call i8* @malloc(i32 20)
  %pC2 = bitcast i8* %pC to i32*

  call void @vadd(i32* %pA, i32* %pB, i32* %pC2)

  call void @printVec(i32* %pC2)


  %pHitler   = call i8* @malloc(i32 20)
  %pHitler.2 = bitcast i8* %pHitler to %Listi*
  %fst       = getelementptr %Listi %pHitler.2, i64 0, i64 0
  call void @printVec2(%Listi* %pHitler.2)


    ; %4 = getelementptr [30 x i8]* @.message1, i32 0, i32 0

    ;  %1 = getelementptr %Exception* %this, i32 0, i32 0
    ; store %Exception_vtable_type* @.Exception_vtable, %Exception_vtable_type** %1

    ; ; save input text string into _text
    ; %2 = getelementptr %Exception* %this, i32 0, i32 1
    ; store i8* %text, i8** %2  

  

  ret i32 42
}

; ; define [5 x i32]* @vadd([5 x i32]* %vec1, [5 x i32]* %vec2)
; ; {
; ; entry:
; ;   %vecc = call @malloc(i64 5) ; alloca [5 x i32]
; ;   br label %loop

; ; loop:
; ;   %i  = phi i32 [0, %entry], [%nexti, %loop]
; ;   %nexti = add i32 %i, 1
; ;   %ptra = getelementptr [5 x i32]* %vec1, i64 0, i32 %i
; ;   %loada = load i32* %ptra
; ;   %ptrb = getelementptr [5 x i32]* %vec2, i64 0, i32 %i
; ;   %loadb = load i32* %ptrb
; ;   %added = add i32 %loada, %loadb
; ;   %ptr = getelementptr [5 x i32]* %vecc, i32 0, i32 %i
; ;   store i32 %added, i32* %ptr
; ;   %eq = icmp eq i32 %i, 4
; ;   br i1 %eq, label %loop, label %exit

; ; exit:
; ;   ret [5 x i32]* %vecc
; ; }


; ; define [5 x i32]* @vadd() ; [5 x i32]* %vec1, [5 x i32]* %vec2)
; ; {
; ;   %vec = alloca [5 x i32]
; ;   %pVec = getelementptr [5 x i32]* %vec, i32 0, i32 0
; ;   store i32 1111, i32* %pVec
; ;   %pVec2 = getelementptr [5 x i32]* %vec, i32 0, i32 1
; ;   store i32 2222, i32* %pVec2

; ; ; pre: 
; ; ;   %vec = alloca [5 x i32]
; ; ;   br label %loop

; ; ; loop:
; ; ;   %i   = phi i32 [ 0,   %pre  ],
; ; ;                  [ %i2, %loop ]
; ; ;   %i2 = add i32 %i, 1

; ; ;   %pVec = getelementptr [5 x i32]* %vec, i32 %i, i32 0
; ; ;   store i32 42, i32* %pVec

; ; ;   call void @butt(i32 %i)
; ; ;   call void @nl()

; ; ;   %cmp = icmp eq i32 %i, 4
; ; ;   br i1 %cmp, label %post, label %loop

; ; ; post:
; ;   ret [5 x i32]* %vec
; ; }


; define i32 @main()
; {
;   %cast = getelementptr [5 x i32], [5 x i32]* @veca, i64 0, i64 0
;   ; ; Convert [13 x i8]* to i8  *...
;   ; %cast = getelementptr [13 x i8], [13 x i8]* @.str, i64 0, i64 0
;   ; getelementptr [@veca = global [5 x i32] [i32 1,  i32 2,  i32 3,  i32 4,  i32 5 ]


;   ; %v = call [5 x i32]* @vadd([5 x i32]* @veca, [5 x i32]* @vecb)
;   ; call void @printVec([5 x i32]* %v)

;   ; %u = call [5 x i32]* @vadd([5 x i32]* @veca, [5 x i32]* @vecb)
;   ; call void @printVec([5 x i32]* %u)

;   ; %j = call [5 x i32]* @vadd([5 x i32]* @veca, [5 x i32]* @vecb)
;   ; call void @printVec([5 x i32]* %j)

;   ret i32 42
; }



; ; declare i8* @malloc(i32) nounwind
; ; declare i32 @puts (i8*)
; ; @global_str = constant [13 x i8] c"Hello World!\00"
; ; define i32 @main() {
; ;   %arr  = call i8* @malloc(i32 10)    ; %3 = malloc(100 * sizeof(X))
; ;   %size = 
; ;   ; %array  = call @malloc [4 x i8 ]                    ; yields {[%4 x i8]*}:array
; ;   ; %size   = add i32 2, 2                        ; yields {i32}:size = i32 4
; ;   ; %array1 = malloc i8, i32 4                    ; yields {i8*}:array1
; ;   ; %array2 = malloc [12 x i8], i32 %size         ; yields {[12 x i8]*}:array2
; ;   ; %array3 = malloc i32, i32 4, align 1024       ; yields {i32*}:array3
; ;   ; %array4 = malloc i32, align 1024              ; yields {i32*}:array4
; ;   %temp = getelementptr [13 x i8]*  @global_str, i32 0, i32 0
; ;   call i32 @puts(i8* %temp)
; ;   ret i32 0
; ; }