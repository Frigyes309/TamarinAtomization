theory XOR_simple_process
begin

builtins: hashing, asymmetric-encryption, signing

restriction Equality:
  "All x y #i. Eq(x,y) @i ==> x = y"

rule NodeA_Setup:
    [
        Fr(~ltkNodeA)
    ]
    -->
    [
        !Ltk($NodeA, ~ltkNodeA),
        !Pk($NodeA, pk(~ltkNodeA)),
        Out(pk(~ltkNodeA))
    ]

rule NodeB_Setup:
    [
        Fr(~ltkNodeB)
    ]
    -->
    [
        !Ltk($NodeB, ~ltkNodeB),
        !Pk($NodeB, pk(~ltkNodeB)),
        Out(pk(~ltkNodeB))
    ]

rule InitState:
    [
        Fr(~ltkUser),
        Fr(~reply_init_vc),
        Fr(~post_init_vc_location)
    ]
    -->
    [
        !Ltk($User, ~ltkUser),
        State($User, <$NodeInit, 'response', ~reply_init_vc, ~post_init_vc_location>)
    ]

rule PathA_Request:
    [
        !Ltk($User, ~ltkUser),
        !Pk($NodeA, pkA),
        //Might have to add ! later on to all States to model malicious User
        State($User, <$NodeInit, 'response', reply_init_vc, post_init_vc_location>),
        Fr(~n)
    ]
    -->
    [ 
        State($User, <$NodeA, 'request', reply_init_vc, post_init_vc_location>),
        Out(aenc(<$User, pk(~ltkUser), reply_init_vc, post_init_vc_location, ~n>, pkA)),
    ]

rule PathB_Request:
    [
        !Ltk($User, ~ltkUser),
        !Pk($NodeB, pkB),
        //Might have to add ! later on to all States to model malicious User
        State($User, <$NodeInit, 'response', reply_init_vc, post_init_vc_location>),
        Fr(~n)
    ]
    -->
    [ 
        State($User, <$NodeB, 'request', reply_init_vc, post_init_vc_location, ~n>),
        Out(aenc(<$User, pk(~ltkUser), reply_init_vc, post_init_vc_location, ~n>, pkB)),
    ]

rule NodeA_Process:
    let 
        content = adec(ciphertext, ~ltkNodeA)
        User = fst(content)
        receivedKey = fst(snd(content))
        current_snake = fst(snd(snd(content)))
        next_location = fst(snd(snd(snd(content))))
        nonce = snd(snd(snd(snd(content))))

        payload = <next_location, ~future_head, h(nonce)>
        signature = sign(payload, ~ltkNodeA)
    in
    [
        In(ciphertext),
        !Ltk($NodeA, ~ltkNodeA),
        Fr(~future_head)
    ]
    --[PathA_Request(User)]->
    [
        !LearnedKeysNodeA($NodeA, <User, receivedKey>),
        Out(aenc(<payload, signature>, receivedKey)),
        State($NodeA, <User, 'response'>)
    ]


rule NodeB_Process:
    let 
        content = adec(ciphertext, ~ltkNodeB)
        User = fst(content)
        receivedKey = fst(snd(content))
        current_snake = fst(snd(snd(content)))
        next_location = fst(snd(snd(snd(content))))
        nonce = snd(snd(snd(snd(content))))

        payload = <next_location, ~future_head, h(nonce)>
        signature = sign(payload, ~ltkNodeB)
    in
    [
        In(ciphertext),
        !Ltk($NodeB, ~ltkNodeB),
        Fr(~future_head)
    ]
    --[PathB_Request(User)]->
    [
        !LearnedKeysNodeB($NodeB, <User, receivedKey>),
        Out(aenc(<payload, signature>, receivedKey)),
        State($NodeB, <User, 'response'>)
    ]

rule User_XOR_Process_A:
    let 
        decrypted_box = adec(ciphertext, ~ltkUser)
        payload = fst(decrypted_box)
        signature = snd(decrypted_box)
        
        current_vc = fst(payload)
        next_vc_location = fst(snd(payload))
        nonce = snd(snd(payload))
    in
    [
        In(ciphertext),
        !Ltk($User, ~ltkUser),
        State($User, <$NodeA, 'request', reply_init_vc, post_init_vc_location, n>),
        !Pk($NodeA, pkNodeA)
    ]
    --[ 
        Eq(h(n), nonce),
        Eq(verify(signature, payload, pkNodeA), true),
        UserPassesNodeA($User, current_vc, next_vc_location)
    ]->
    [
        State($User, <$NodeA, 'response', current_vc, next_vc_location>)
    ]
    

rule User_XOR_Process_B:
    let 
        decrypted_box = adec(ciphertext, ~ltkUser)
        payload = fst(decrypted_box)
        signature = snd(decrypted_box)

        current_vc = fst(payload)
        next_vc_location = fst(snd(payload))
        nonce = snd(snd(payload))
    in
    [
        In(ciphertext),
        !Ltk($User, ~ltkUser),
        State($User, <$NodeB, 'request', reply_init_vc, post_init_vc_location, n>),
        !Pk($NodeB, pkNodeB)
    ]
    --[ 
        Eq(h(n), nonce),
        Eq(verify(signature, payload, pkNodeB), true),
        UserPassesNodeB($User, current_vc, next_vc_location) 
    ]->
    [
        State($User, <$NodeB, 'response', current_vc, next_vc_location>)
    ]

lemma User_XOR_AB:
    "All user current_vc next_vc_location #i.
        UserPassesNodeA(user, current_vc, next_vc_location) @i
        ==> 
        not (Ex #j. UserPassesNodeB(user, current_vc, next_vc_location) @j)"

lemma User_XOR_BA:
    "All user current_vc next_vc_location #i.
        UserPassesNodeB(user, current_vc, next_vc_location) @i
        ==> 
        not (Ex #j. UserPassesNodeA(user, current_vc, next_vc_location) @j)"

lemma User_Got_ReponseA:
    exists-trace
    "Ex user a b #i.
        UserPassesNodeA(user, a, b) @i"

lemma User_Got_ReponseB:
    exists-trace
    "Ex user a b #i.
        UserPassesNodeB(user, a, b) @i"

lemma PathA_Key_Secretary:
    "All user vc next #i.
        UserPassesNodeA(user, vc, next) @i
        ==>
        (not (Ex #j. K(vc) @j))
        & (not (Ex #k. K(next) @k))"

lemma PathB_Key_Secretary:
    "All user vc next #i.
        UserPassesNodeB(user, vc, next) @i
        ==>
        (not (Ex #j. K(vc) @j))
        & (not (Ex #k. K(next) @k))"
end