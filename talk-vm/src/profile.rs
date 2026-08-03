#[inline(always)]
pub(crate) fn init() {
    #[cfg(feature = "profile-tracy")]
    {
        static CLIENT: std::sync::OnceLock<profiling::tracy_client::Client> =
            std::sync::OnceLock::new();
        CLIENT.get_or_init(profiling::tracy_client::Client::start);
    }
}
