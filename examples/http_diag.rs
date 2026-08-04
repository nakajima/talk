fn main() {
    let result = std::panic::catch_unwind(|| {
        let _ = talk::compiling::stdlib::module_with_id("http");
    });
    if let Err(payload) = result {
        if let Some(msg) = payload.downcast_ref::<String>() {
            println!("{msg}");
        } else if let Some(msg) = payload.downcast_ref::<&str>() {
            println!("{msg}");
        }
    }
}
