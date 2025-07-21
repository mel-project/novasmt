use thiserror::Error;

#[derive(Error, Debug)]
pub enum SmtError {
    #[error("I/O error in node database: {0:?}")]
    IoError(std::io::Error),

    #[error("corrupt data in node database: {0:?}")]
    DbCorrupt(anyhow::Error),
}
