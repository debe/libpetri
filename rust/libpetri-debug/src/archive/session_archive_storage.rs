//! Storage backend trait for session archives.

/// Summary of an archived session in storage.
#[derive(Debug, Clone)]
pub struct ArchivedSessionSummary {
    pub session_id: String,
    pub key: String,
    pub size_bytes: u64,
    /// Epoch milliseconds.
    pub last_modified: u64,
}

/// Storage backend interface for session archives.
pub trait SessionArchiveStorage: Send + Sync {
    /// Stores a compressed archive for the given session.
    fn store(&self, session_id: &str, data: &[u8]) -> Result<(), String>;

    /// Lists archived sessions, most recent first.
    fn list(
        &self,
        limit: usize,
        prefix: Option<&str>,
    ) -> Result<Vec<ArchivedSessionSummary>, String>;

    /// Retrieves the compressed archive data for a session.
    fn retrieve(&self, session_id: &str) -> Result<Vec<u8>, String>;

    /// Returns `true` if the storage backend is available.
    fn is_available(&self) -> bool;
}
