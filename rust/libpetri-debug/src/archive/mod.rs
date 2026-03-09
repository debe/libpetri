//! Session archive support for persisting and replaying debug sessions.

mod session_archive;
mod session_archive_storage;

#[cfg(feature = "archive")]
mod session_archive_reader;
#[cfg(feature = "archive")]
mod session_archive_writer;

pub use session_archive::{CURRENT_VERSION, SessionArchive};
pub use session_archive_storage::{ArchivedSessionSummary, SessionArchiveStorage};

#[cfg(feature = "archive")]
pub use session_archive_reader::{ImportedSession, SessionArchiveReader};
#[cfg(feature = "archive")]
pub use session_archive_writer::SessionArchiveWriter;
