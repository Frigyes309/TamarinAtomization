theory Init_process
begin

builtins: hashing, asymmetric-encryption, signing

rule Init_NodeInit:
    [
        Fr(~ltkNodeInit)
    ]
    -->
    [
        !Ltk($NodeInit, ~ltkNodeInit),
        !Pk($NodeInit, pk(~ltkNodeInit)),
        Out(pk(~ltkNodeInit))
    ]

rule Init_User:
    [
        Fr(~ltkUser)
    ]
    --[ UserCreated($User, ~ltkUser) ]->
    [
        !Ltk($User, ~ltkUser)
    ]

rule Init_User_Request:
    [
        !Ltk($User, ~ltkUser),
        !Pk($NodeInit, pkNodeInit),
        Fr(~init_vc),
        Fr(~init_message),
        Fr(~n)
    ]
    -->
    [
        Out(aenc(<$User, pk(~ltkUser), ~init_vc, ~init_message, ~n>, pkNodeInit)),
        State($User, <$NodeInit, 'request', ~init_vc, ~init_message, ~n>)
    ]

rule NodeInit_Process:
    let 
        content = adec(ciphertext, ~ltkNodeInit)
        User = fst(content)
        receivedKey = fst(snd(content))
        init_vc = fst(snd(snd(content)))
        init_message = fst(snd(snd(snd(content))))
        nonce = snd(snd(snd(snd(content))))

        payload = <~reply_init_vc, ~post_init_vc_location, h(nonce)>
        signature = sign(payload, ~ltkNodeInit)
    in
    [
        In(ciphertext),
        !Ltk($NodeInit, ~ltkNodeInit),
        Fr(~reply_init_vc),
        Fr(~post_init_vc_location)
    ]
    --[ Finished($NodeInit, User) ]->
    [
        !LearnedKeysNodeInit($NodeInit, <User, receivedKey>),
        Out(aenc(<payload, signature>, receivedKey)),
        State($NodeInit, <User, 'init'>)
    ]

rule User_Branching:
    let 
        decrypted_box = adec(reply_ciphertext, ~ltkUser)
        payload = fst(decrypted_box)
        signature = snd(decrypted_box)

        reply_init_vc = fst(payload)
        post_init_vc_location = fst(snd(payload))
        nonce = snd(snd(payload))
    in
    [
        In(reply_ciphertext),
        State($User, <$NodeInit, 'request', init_vc, init_message, n>),
        !Ltk($User, ~ltkUser),
        !Pk($NodeInit, pkNodeInit),
        Eq(h(n), nonce) 
    ]
    --[ User_Passes_Initialization($User, reply_init_vc, post_init_vc_location) ]->
    [
        Eq(verify(signature, payload, pkNodeInit), true),
        State($User, <$NodeInit, 'response', reply_init_vc, post_init_vc_location>)
    ]


lemma User_Key_Secretary:
    "All user key #i.
        UserCreated(user, key) @i
        ==>
        not (Ex #j. K(key) @j)"

lemma Functional_Test:
    exists-trace
    "Ex node user #i.
        Finished(node, user) @i"

lemma User_Receives_Response:
    "All user reply_vc loc #i.
        User_Passes_Initialization(user, reply_vc, loc) @i
        ==>
        ( not (Ex #j. K(reply_vc) @j) )
        &
        ( not (Ex #k. K(loc) @k) )"    

end