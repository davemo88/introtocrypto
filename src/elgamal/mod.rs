
// Message
struct Message {
    a: u64,
    p: u64,
}

struct Keys {
    public: u128,
    private: u128,
    other_private: u128,
}

impl Keys {
    fn public(&self) -> u128 {
        self.public
    }

    fn private(&self) -> u128 {
        self.private
    }

    fn make_message(&self, _message: &str) -> Message {
        let dummy = 0;
        Message{a: dummy, p: dummy}
    }

    fn decode_message(&self, _message: Message) -> Message {
        Message{a: 0, p: 0}
    }

    fn assert(&self) {
        for _i in 1..10 {

        }
    }
}

fn generate_keys() -> Keys {
    let public = 7;
    let private = 5; // a
    let other_private = 0;
    Keys{public, private, other_private}
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_generate_keys() {
        let keys = generate_keys();
        assert_eq!(keys.public(), 7);
        assert_eq!(keys.private(), 5);
        assert_eq!(keys.other_private, 0);
    }

    #[test]
    fn test_what() {
        let keys = generate_keys();
        keys.assert();
    }

    #[test]
    fn test_message() {
        let alice = generate_keys();
        let bob = generate_keys();
        let source = "how soon is now?";
        let encrypted = alice.make_message(source);
        let decrypted = bob.decode_message(encrypted);

        assert_eq!(decrypted.a, 0);
        assert_eq!(decrypted.p, 0);
    }
}
