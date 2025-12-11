theory AND_process
begin

builtins: hashing, asymmetric-encryption, signing

include(`./raw/init.spthy.raw')
// ')

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

rule TransferState:
    let 
        pkA = pk(~ltkNodeA)
        pkB = pk(~ltkNodeB)
    in
    [
        State($User, <$NodeInit, 'response', reply_init_vc, post_init_vc_location>),
        Fr(~post_init_vc_locationB),
        !Pk($NodeA, pkA),
        !Pk($NodeB, pkB),
    ]
    -->
    [
        State($User, <$NodeInit, 'response', reply_init_vc, post_init_vc_locationA, pkA>),
        State($User, <$NodeInit, 'response', reply_init_vc, post_init_vc_locationB, pkB>)
    ]

rule PathA_Request:
    [
        !Ltk($User, ~ltkUser),
        !Pk($NodeA, pk(~ltkNodeA)),
        //Might have to add ! later on to all States to model malicious User
        State($User, <$NodeInit, 'response', reply_init_vc, post_init_vc_locationA, pkA>),
        Fr(~nA)
    ]
    --[    ]->
    [ 
        State($User, <$NodeA, 'request', reply_init_vc, post_init_vc_locationA, ~nA>),
        Out(aenc(<$User, pk(~ltkUser), reply_init_vc, post_init_vc_locationA, ~nA>, pk(~ltkNodeA))),
    ]

rule PathB_Request:
    [
        !Ltk($User, ~ltkUser),
        !Pk($NodeB, pk(~ltkNodeB)),
        //Might have to add ! later on to all States to model malicious User
        State($User, <$NodeInit, 'response', reply_init_vc, post_init_vc_locationB, pkB>),
        Fr(~nB)
    ]
    --[    ]->
    [ 
        State($User, <$NodeB, 'request', reply_init_vc, post_init_vc_locationB, ~nB>),
        Out(aenc(<$User, pk(~ltkUser), reply_init_vc, post_init_vc_locationB, ~nB>, pk(~ltkNodeB)))
    ]

// At an AND gate always NodeA gives the next head
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
    --[ PathA_Response(User) ]->
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

        payload = <next_location, h(nonce)>
        signature = sign(payload, ~ltkNodeB)
    in
    [
        In(ciphertext),
        !Ltk($NodeB, ~ltkNodeB),
    ]
    --[ PathB_Response(User) ]->
    [
        !LearnedKeysNodeB($NodeB, <User, receivedKey>),
        Out(aenc(<payload, signature>, receivedKey)),
        State($NodeB, <User, 'response'>)
    ]

rule User_AND_Process:
    let 
        decrypted_boxA = adec(ciphertextA, ~ltkUser)
        payloadA = fst(decrypted_boxA)
        signatureA = snd(decrypted_boxA)
        
        current_vcA = fst(payloadA)
        next_vc_location = fst(snd(payloadA))
        nonceA = snd(snd(payloadA))

        decrypted_boxB = adec(ciphertextB, ~ltkUser)
        payloadB = fst(decrypted_boxB)
        signatureB = snd(decrypted_boxB)
        
        current_vcB = fst(payloadB)
        nonceB = snd(payloadB)
    in
    [
        In(ciphertextA),
        In(ciphertextB),
        !Ltk($User, ~ltkUser),
        State($User, <$NodeA, 'request', reply_init_vc, post_init_vc_locationA, ~nA>),
        State($User, <$NodeB, 'request', reply_init_vc, post_init_vc_locationB, ~nB>),
        !Pk($NodeA, pkNodeA),
        !Pk($NodeA, pkNodeB)
    ]
    --[ 
        Eq(h(nA), nonceA),
        Eq(h(nB), nonceB),
        UserPassesNode($User, current_vc, next_vc_location)
    ]->
    [
        Eq(verify(signatureA, payloadA, pkNodeA), true),
        Eq(verify(signatureB, payloadB, pkNodeB), true),
        State($User, <$NodeA, 'response', current_vc, next_vc_location>) // Maybe we need a sum node here
    ]

lemma User_Got_AND_Reponse:
    exists-trace
    "Ex user a b #i.
        UserPassesNode(user, a, b) @i"

lemma User_Got_Response_From_A:
    exists-trace
    "Ex user a b #i.
        PathB_Response(user) @i"

lemma User_Got_Response_From_B:
    exists-trace
    "Ex user a b #i.
        PathB_Response(user) @i"

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